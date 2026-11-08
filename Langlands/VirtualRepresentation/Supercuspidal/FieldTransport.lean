import Langlands.VirtualRepresentation.Supercuspidal.Basic
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Unitary.Restriction
import Langlands.Weil.Local.ExtensionResidue

/-!
# Supercuspidal lattices along an isomorphism of topological fields

A field isomorphism `σ : F ≃+* E` that is a homeomorphism acts entrywise on
general linear groups. Pulling representations of `GL_n(E)` back along this
isomorphism preserves smoothness, irreducibility, supercuspidality and
unitarizability. It therefore gives bijections of supercuspidal classes and
integral lattice equivalences, from `E` to `F`.
-/

noncomputable section

open CategoryTheory

universe uF uE uV

namespace Langlands.GeneralLinear

variable {F : Type uF} {E : Type uE} [Field F] [Field E]
  [TopologicalSpace F] [TopologicalSpace E]

/-- Entrywise transport along a homeomorphic field isomorphism. -/
def fieldEquiv (n : ℕ) (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm) :
    GeneralLinear n F ≃ₜ* GeneralLinear n E where
  toFun := Matrix.GeneralLinearGroup.map σ.toRingHom
  invFun := Matrix.GeneralLinearGroup.map σ.symm.toRingHom
  left_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact σ.symm_apply_apply (g i j)
  right_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact σ.apply_symm_apply (g i j)
  map_mul' := map_mul _
  continuous_toFun := hσ.generalLinearGroup_map
  continuous_invFun := hσs.generalLinearGroup_map

variable (n : ℕ) (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm)

@[simp]
theorem fieldEquiv_apply (g : GeneralLinear n F) (i j : Fin n) :
    fieldEquiv n σ hσ hσs g i j = σ (g i j) := rfl

theorem fieldEquiv_symm : (fieldEquiv n σ hσ hσs).symm = fieldEquiv n σ.symm hσs hσ := rfl

namespace BlockShape

variable {n} (B : BlockShape n)

/-- The standard block parabolic is the preimage of the corresponding parabolic. -/
theorem parabolic_comap_fieldEquiv :
    (B.parabolic E).comap (fieldEquiv n σ hσ hσs).toMonoidHom = B.parabolic F := by
  ext g
  rw [Subgroup.mem_comap, mem_parabolic_iff, mem_parabolic_iff]
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun a =>
    forall_congr' fun b => forall_congr' fun _ => ?_
  exact map_eq_zero_iff σ σ.injective

/-- The standard block unipotent subgroup is the preimage of the corresponding one. -/
theorem unipotentSubgroup_comap_fieldEquiv :
    (B.unipotentSubgroup E).comap (fieldEquiv n σ hσ hσs).toMonoidHom =
      B.unipotentSubgroup F := by
  ext g
  rw [Subgroup.mem_comap, mem_unipotentSubgroup_iff, mem_unipotentSubgroup_iff]
  refine and_congr ?_ (forall_congr' fun i => forall_congr' fun a =>
    forall_congr' fun b => ?_)
  · rw [← parabolic_comap_fieldEquiv σ hσ hσs B, Subgroup.mem_comap]
  · change σ (g (B.index i a) (B.index i b)) = _ ↔ _
    split_ifs
    · exact map_eq_one_iff σ σ.injective
    · exact map_eq_zero_iff σ σ.injective

/-- The image of the standard block unipotent subgroup is the corresponding one. -/
theorem unipotentSubgroup_map_fieldEquiv :
    (B.unipotentSubgroup F).map (fieldEquiv n σ hσ hσs).toMonoidHom =
      B.unipotentSubgroup E := by
  rw [← unipotentSubgroup_comap_fieldEquiv σ hσ hσs B]
  exact Subgroup.map_comap_eq_self_of_surjective (fieldEquiv n σ hσ hσs).surjective _

/-- Conjugate unipotent subgroups correspond under the entrywise transport. -/
theorem conjugateUnipotent_map_fieldEquiv (g : GeneralLinear n F) :
    (B.conjugateUnipotent g).map (fieldEquiv n σ hσ hσs).toMonoidHom =
      B.conjugateUnipotent (fieldEquiv n σ hσ hσs g) := by
  have hc : (fieldEquiv n σ hσ hσs).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (fieldEquiv n σ hσ hσs g)).toMonoidHom.comp
        (fieldEquiv n σ hσ hσs).toMonoidHom := by
    ext x : 1
    change fieldEquiv n σ hσ hσs (g * x * g⁻¹) =
      fieldEquiv n σ hσ hσs g * fieldEquiv n σ hσ hσs x * (fieldEquiv n σ hσ hσs g)⁻¹
    rw [map_mul, map_mul, map_inv]
  rw [conjugateUnipotent, conjugateUnipotent, Subgroup.map_map, hc, ← Subgroup.map_map,
    unipotentSubgroup_map_fieldEquiv]

include σ hσ hσs in
/-- A block parabolic is proper over `F` exactly when it is proper over `E`. -/
theorem parabolic_ne_top_fieldEquiv_iff :
    B.parabolic F ≠ ⊤ ↔ B.parabolic E ≠ ⊤ := by
  rw [← parabolic_comap_fieldEquiv σ hσ hσs B]
  constructor
  · intro h hE
    exact h (by rw [hE, Subgroup.comap_top])
  · intro h hF
    apply h
    rw [eq_top_iff]
    intro g _
    have hg : (fieldEquiv n σ hσ hσs).symm g ∈
        (B.parabolic E).comap (fieldEquiv n σ hσ hσs).toMonoidHom := by
      rw [hF]
      exact Subgroup.mem_top _
    change fieldEquiv n σ hσ hσs ((fieldEquiv n σ hσ hσs).symm g) ∈ B.parabolic E at hg
    rwa [ContinuousMulEquiv.apply_symm_apply] at hg

end BlockShape

section Supercuspidal

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Pullback along the entrywise transport preserves supercuspidality. -/
theorem isSupercuspidal_comp_fieldEquiv (ρ : Representation ℂ (GeneralLinear n E) V)
    (hρ : IsSupercuspidal ρ) :
    IsSupercuspidal (ρ.comp (fieldEquiv n σ hσ hσs).toMonoidHom) := by
  refine ⟨isAdmissible_comp_continuousMulEquiv ρ (fieldEquiv n σ hσ hσs) hρ.1, ?_⟩
  intro B hB g
  have hvan := hρ.2 B ((B.parabolic_ne_top_fieldEquiv_iff σ hσ hσs).mp hB)
    (fieldEquiv n σ hσ hσs g)
  rw [← B.conjugateUnipotent_map_fieldEquiv σ hσ hσs g] at hvan
  exact ⟨fun x y => (Jacquet.coinvariantsMapEquiv ρ (fieldEquiv n σ hσ hσs).toMonoidHom
    (B.conjugateUnipotent g)).injective (hvan.elim _ _)⟩

/-- Pullback along the entrywise transport preserves and reflects supercuspidality. -/
theorem isSupercuspidal_comp_fieldEquiv_iff (ρ : Representation ℂ (GeneralLinear n E) V) :
    IsSupercuspidal (ρ.comp (fieldEquiv n σ hσ hσs).toMonoidHom) ↔ IsSupercuspidal ρ := by
  refine ⟨fun h => ?_, isSupercuspidal_comp_fieldEquiv n σ hσ hσs ρ⟩
  have h' := isSupercuspidal_comp_fieldEquiv n σ.symm hσs hσ _ h
  have heq : (ρ.comp (fieldEquiv n σ hσ hσs).toMonoidHom).comp
      (fieldEquiv n σ.symm hσs hσ).toMonoidHom = ρ := by
    ext g v
    change ρ (fieldEquiv n σ hσ hσs ((fieldEquiv n σ hσ hσs).symm g)) v = ρ g v
    rw [ContinuousMulEquiv.apply_symm_apply]
  rwa [heq] at h'

end Supercuspidal

namespace SupercuspidalRep

variable {n σ hσ hσs}

/-- Pull back an actual supercuspidal representation of `GL_n(E)` to `GL_n(F)`. -/
def fieldPullback (A : SupercuspidalRep.{uE, uV} (F := E) (n := n)) :
    SupercuspidalRep.{uF, uV} (F := F) (n := n) :=
  ⟨SmoothRep.pullback (fieldEquiv n σ hσ hσs) A.obj,
    (isIrreducible_comp_continuousMulEquiv_iff A.obj.representation
      (fieldEquiv n σ hσ hσs)).mpr A.property.1,
    isSupercuspidal_comp_fieldEquiv n σ hσ hσs A.obj.representation A.property.2⟩

variable (σ hσ hσs) in
@[simp]
theorem fieldPullback_representation (A : SupercuspidalRep.{uE, uV} (F := E) (n := n)) :
    (fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A).obj.representation =
      A.obj.representation.comp (fieldEquiv n σ hσ hσs).toMonoidHom := rfl

/-- Isomorphisms of supercuspidal representatives pull back to isomorphisms. -/
def fieldPullbackIso {A B : SupercuspidalRep.{uE, uV} (F := E) (n := n)} (f : A ≅ B) :
    fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A ≅
      fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) B :=
  ObjectProperty.isoMk _ ((SmoothRep.pullbackFunctor (fieldEquiv n σ hσ hσs)).mapIso
    ((supercuspidalProperty (F := E) (n := n)).ι.mapIso f))

variable (σ hσ hσs) in
/-- Pulling back along `σ` and then along `σ.symm` recovers the representative,
through the identity map of its space. -/
def fieldPullbackSymmIso (A : SupercuspidalRep.{uE, uV} (F := E) (n := n)) :
    fieldPullback (σ := σ.symm) (hσ := hσs) (hσs := hσ)
        (fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A) ≅ A :=
  ObjectProperty.isoMk _ (SmoothRep.mkIso
    (Representation.Equiv.mk (LinearEquiv.refl ℂ A.obj) (fun g => by
      ext v
      change A.obj.representation (fieldEquiv n σ hσ hσs ((fieldEquiv n σ hσ hσs).symm g)) v =
        A.obj.representation g v
      rw [ContinuousMulEquiv.apply_symm_apply])))

end SupercuspidalRep

namespace SupercuspidalClass

variable {n}

/-- Pullback of supercuspidal classes from `GL_n(E)` to `GL_n(F)`. -/
def fieldPullback :
    SupercuspidalClass.{uV, uE} (F := E) (n := n) →
      SupercuspidalClass.{uV, uF} (F := F) (n := n) :=
  Quotient.map (SupercuspidalRep.fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs))
    (fun _ _ ⟨f⟩ => ⟨SupercuspidalRep.fieldPullbackIso f⟩)

@[simp]
theorem fieldPullback_isoClass (A : SupercuspidalRep.{uE, uV} (F := E) (n := n)) :
    fieldPullback σ hσ hσs A.isoClass =
      (SupercuspidalRep.fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A).isoClass := rfl

@[simp]
theorem fieldPullback_symm_fieldPullback (a : SupercuspidalClass.{uV, uE} (F := E) (n := n)) :
    fieldPullback σ.symm hσs hσ (fieldPullback σ hσ hσs a) = a := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨SupercuspidalRep.fieldPullbackSymmIso σ hσ hσs A⟩

@[simp]
theorem fieldPullback_fieldPullback_symm (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    fieldPullback σ hσ hσs (fieldPullback σ.symm hσs hσ a) = a :=
  fieldPullback_symm_fieldPullback σ.symm hσs hσ a

/-- The bijection of supercuspidal classes induced by pullback along `σ`. -/
def fieldPullbackEquiv (n : ℕ) :
    SupercuspidalClass.{uV, uE} (F := E) (n := n) ≃
      SupercuspidalClass.{uV, uF} (F := F) (n := n) where
  toFun := fieldPullback σ hσ hσs
  invFun := fieldPullback σ.symm hσs hσ
  left_inv := fieldPullback_symm_fieldPullback σ hσ hσs
  right_inv := fieldPullback_fieldPullback_symm σ hσ hσs

@[simp]
theorem fieldPullbackEquiv_symm (n : ℕ) :
    (fieldPullbackEquiv σ hσ hσs n).symm = fieldPullbackEquiv σ.symm hσs hσ n := rfl

/-- Pullback along `σ` preserves unitarizability of classes. -/
theorem isUnitarizable_fieldPullback (a : SupercuspidalClass.{uV, uE} (F := E) (n := n))
    (ha : a.IsUnitarizable) : (fieldPullback σ hσ hσs a).IsUnitarizable := by
  induction a using Quotient.inductionOn with
  | h A => exact Langlands.IsUnitarizable.comp ha (fieldEquiv n σ hσ hσs).toMonoidHom

/-- Pullback along `σ` preserves and reflects unitarizability of classes. -/
theorem isUnitarizable_fieldPullback_iff (a : SupercuspidalClass.{uV, uE} (F := E) (n := n)) :
    (fieldPullback σ hσ hσs a).IsUnitarizable ↔ a.IsUnitarizable := by
  refine ⟨fun h => ?_, isUnitarizable_fieldPullback σ hσ hσs a⟩
  have h' := isUnitarizable_fieldPullback σ.symm hσs hσ _ h
  rwa [fieldPullback_symm_fieldPullback] at h'

end SupercuspidalClass

end Langlands.GeneralLinear

namespace Langlands.VirtualRepresentation.Supercuspidal

open GeneralLinear

variable {F : Type uF} {E : Type uE} [Field F] [Field E]
  [TopologicalSpace F] [TopologicalSpace E]
  (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm)

/-- Pull back each supercuspidal class of `E` along `σ`, retaining its rank. -/
def fieldBasisEquiv : Basis.{uE, uV} E ≃ Basis.{uF, uV} F :=
  Equiv.sigmaCongrRight (fun n => SupercuspidalClass.fieldPullbackEquiv σ hσ hσs (n : ℕ))

@[simp]
theorem fieldBasisEquiv_rank (b : Basis.{uE, uV} E) :
    (fieldBasisEquiv σ hσ hσs b).1 = b.1 := rfl

@[simp]
theorem fieldBasisEquiv_symm :
    (fieldBasisEquiv.{uF, uE, uV} σ hσ hσs).symm = fieldBasisEquiv σ.symm hσs hσ := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  rfl

/-- On representatives, the basis bijection is pullback along `σ`. -/
theorem fieldBasisEquiv_basisClass (n : ℕ+)
    (A : SupercuspidalRep.{uE, uV} (F := E) (n := (n : ℕ))) :
    fieldBasisEquiv σ hσ hσs (basisClass n A) =
      basisClass n (SupercuspidalRep.fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A) := rfl

/-- Pullback along `σ` preserves and reflects the unitary predicate. -/
theorem isUnitaryClass_fieldBasisEquiv_iff (b : Basis.{uE, uV} E) :
    IsUnitaryClass F (fieldBasisEquiv σ hσ hσs b) ↔ IsUnitaryClass E b :=
  SupercuspidalClass.isUnitarizable_fieldPullback_iff σ hσ hσs b.2

/-- Restrict the basis bijection to the unitary bases. -/
def fieldUnitaryBasisEquiv : UnitaryBasis.{uE, uV} E ≃ UnitaryBasis.{uF, uV} F :=
  (fieldBasisEquiv σ hσ hσs).subtypeEquiv (fun b =>
    (isUnitaryClass_fieldBasisEquiv_iff σ hσ hσs b).symm)

@[simp]
theorem fieldUnitaryBasisEquiv_val (b : UnitaryBasis.{uE, uV} E) :
    (fieldUnitaryBasisEquiv σ hσ hσs b).val = fieldBasisEquiv σ hσ hσs b.val := rfl

@[simp]
theorem fieldUnitaryBasisEquiv_symm :
    (fieldUnitaryBasisEquiv.{uF, uE, uV} σ hσ hσs).symm =
      fieldUnitaryBasisEquiv σ.symm hσs hσ := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (fieldBasisEquiv_symm σ hσ hσs) b.val

/-- On a unitary representative, the unitary basis bijection is pullback along `σ`. -/
theorem fieldUnitaryBasisEquiv_unitaryBasisClass (n : ℕ+)
    (A : SupercuspidalRep.{uE, uV} (F := E) (n := (n : ℕ)))
    (hu : Langlands.IsUnitarizable A.obj.representation) :
    fieldUnitaryBasisEquiv σ hσ hσs (unitaryBasisClass n A hu) =
      unitaryBasisClass n (SupercuspidalRep.fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A)
        (Langlands.IsUnitarizable.comp hu (fieldEquiv n σ hσ hσs).toMonoidHom) := rfl

/-- Pullback along `σ` on the full supercuspidal lattices. -/
def fieldLatticeEquiv : Lattice.{uE, uV} E ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  reindex (fieldBasisEquiv σ hσ hσs)

@[simp]
theorem fieldLatticeEquiv_single (b : Basis.{uE, uV} E) (m : ℤ) :
    fieldLatticeEquiv σ hσ hσs (Finsupp.single b m) =
      Finsupp.single (fieldBasisEquiv σ hσ hσs b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem fieldLatticeEquiv_generator (b : Basis.{uE, uV} E) :
    fieldLatticeEquiv σ hσ hσs (generator b) = generator (fieldBasisEquiv σ hσ hσs b) :=
  fieldLatticeEquiv_single σ hσ hσs b 1

@[simp]
theorem fieldLatticeEquiv_coefficient (x : Lattice.{uE, uV} E) (b : Basis.{uE, uV} E) :
    fieldLatticeEquiv σ hσ hσs x (fieldBasisEquiv σ hσ hσs b) = x b := by
  change x ((fieldBasisEquiv σ hσ hσs).symm (fieldBasisEquiv σ hσ hσs b)) = x b
  rw [Equiv.symm_apply_apply]

@[simp]
theorem fieldLatticeEquiv_symm :
    (fieldLatticeEquiv.{uF, uE, uV} σ hσ hσs).symm = fieldLatticeEquiv σ.symm hσs hσ := by
  simp [fieldLatticeEquiv, reindex]

/-- A supercuspidal generator goes to the generator of the pulled-back representative. -/
theorem fieldLatticeEquiv_ofRepresentation (n : ℕ+)
    (A : SupercuspidalRep.{uE, uV} (F := E) (n := (n : ℕ))) :
    fieldLatticeEquiv σ hσ hσs (ofRepresentation n A) =
      ofRepresentation n (SupercuspidalRep.fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A) :=
  fieldLatticeEquiv_generator σ hσ hσs _

/-- Pullback along `σ` on the unitary supercuspidal lattices. -/
def fieldUnitaryLatticeEquiv : UnitaryLattice.{uE, uV} E ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  reindex (fieldUnitaryBasisEquiv σ hσ hσs)

@[simp]
theorem fieldUnitaryLatticeEquiv_single (b : UnitaryBasis.{uE, uV} E) (m : ℤ) :
    fieldUnitaryLatticeEquiv σ hσ hσs (Finsupp.single b m) =
      Finsupp.single (fieldUnitaryBasisEquiv σ hσ hσs b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem fieldUnitaryLatticeEquiv_generator (b : UnitaryBasis.{uE, uV} E) :
    fieldUnitaryLatticeEquiv σ hσ hσs (generator b) =
      generator (fieldUnitaryBasisEquiv σ hσ hσs b) :=
  fieldUnitaryLatticeEquiv_single σ hσ hσs b 1

@[simp]
theorem fieldUnitaryLatticeEquiv_coefficient (x : UnitaryLattice.{uE, uV} E)
    (b : UnitaryBasis.{uE, uV} E) :
    fieldUnitaryLatticeEquiv σ hσ hσs x (fieldUnitaryBasisEquiv σ hσ hσs b) = x b := by
  change x ((fieldUnitaryBasisEquiv σ hσ hσs).symm (fieldUnitaryBasisEquiv σ hσ hσs b)) = x b
  rw [Equiv.symm_apply_apply]

@[simp]
theorem fieldUnitaryLatticeEquiv_symm :
    (fieldUnitaryLatticeEquiv.{uF, uE, uV} σ hσ hσs).symm =
      fieldUnitaryLatticeEquiv σ.symm hσs hσ := by
  simp [fieldUnitaryLatticeEquiv, reindex]

/-- A unitary supercuspidal generator goes to the generator of the pulled-back
representative. -/
theorem fieldUnitaryLatticeEquiv_ofUnitaryRepresentation (n : ℕ+)
    (A : SupercuspidalRep.{uE, uV} (F := E) (n := (n : ℕ)))
    (hu : Langlands.IsUnitarizable A.obj.representation) :
    fieldUnitaryLatticeEquiv σ hσ hσs (ofUnitaryRepresentation n A hu) =
      ofUnitaryRepresentation n
        (SupercuspidalRep.fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A)
        (Langlands.IsUnitarizable.comp hu (fieldEquiv n σ hσ hσs).toMonoidHom) :=
  fieldUnitaryLatticeEquiv_generator σ hσ hσs _

/-- Inclusion of the unitary lattices intertwines the two pullbacks. -/
@[simp]
theorem includeUnitary_fieldUnitaryLatticeEquiv (x : UnitaryLattice.{uE, uV} E) :
    includeUnitary F (fieldUnitaryLatticeEquiv σ hσ hσs x) =
      fieldLatticeEquiv σ hσ hσs (includeUnitary E x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [includeUnitary, includeSubset, map]

/-- Pullback preserves the rank-weighted integral degree. -/
@[simp]
theorem degree_fieldLatticeEquiv (x : Lattice.{uE, uV} E) :
    degree F (fieldLatticeEquiv σ hσ hσs x) = degree E x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    simp [degree, rankedDegree, VirtualRepresentation.degree, extend]

@[simp]
theorem unitaryDegree_fieldUnitaryLatticeEquiv (x : UnitaryLattice.{uE, uV} E) :
    unitaryDegree F (fieldUnitaryLatticeEquiv σ hσ hσs x) = unitaryDegree E x := by
  simp [unitaryDegree]

/-- Pullback preserves the coefficient pairing. -/
theorem multiplicityPairing_fieldLatticeEquiv (x y : Lattice.{uE, uV} E) :
    multiplicityPairing F (fieldLatticeEquiv σ hσ hσs x) (fieldLatticeEquiv σ hσ hσs y) =
      multiplicityPairing E x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m =>
    simp [multiplicityPairing, pairing, extend, coefficient]

/-- Pullback preserves the unitary coefficient pairing. -/
theorem unitaryPairing_fieldUnitaryLatticeEquiv (x y : UnitaryLattice.{uE, uV} E) :
    unitaryPairing F (fieldUnitaryLatticeEquiv σ hσ hσs x)
        (fieldUnitaryLatticeEquiv σ hσ hσs y) =
      unitaryPairing E x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m =>
    simp [unitaryPairing, pairing, extend, coefficient]

end Langlands.VirtualRepresentation.Supercuspidal

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- An isomorphism of p-adic fields is continuous for the canonical topologies. -/
theorem continuous_algEquiv :
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    Continuous f := by
  let := F.canonicalNormedField
  let := E.canonicalNormedField
  exact (Weil.Local.extension_isometry F E f.toAlgHom).continuous

/-- Pullback along an isomorphism of p-adic fields on unitary supercuspidal bases. -/
def unitaryBasisEquiv : UnitaryBasis.{uE, uV} E ≃ UnitaryBasis.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  letI := E.canonicalTopologicalData.topology
  Supercuspidal.fieldUnitaryBasisEquiv f.toRingEquiv (continuous_algEquiv F E f)
    (continuous_algEquiv E F f.symm)

/-- Pullback along an isomorphism of p-adic fields on the full supercuspidal lattices. -/
def latticeEquiv : Lattice.{uE, uV} E ≃ₗ[ℤ] Lattice.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  letI := E.canonicalTopologicalData.topology
  Supercuspidal.fieldLatticeEquiv f.toRingEquiv (continuous_algEquiv F E f)
    (continuous_algEquiv E F f.symm)

/-- Pullback along an isomorphism of p-adic fields on the unitary supercuspidal
lattices. -/
def unitaryLatticeEquiv : UnitaryLattice.{uE, uV} E ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  letI := E.canonicalTopologicalData.topology
  Supercuspidal.fieldUnitaryLatticeEquiv f.toRingEquiv (continuous_algEquiv F E f)
    (continuous_algEquiv E F f.symm)

@[simp]
theorem unitaryLatticeEquiv_generator (b : UnitaryBasis.{uE, uV} E) :
    unitaryLatticeEquiv F E f (generator b) = generator (unitaryBasisEquiv F E f b) := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  exact Supercuspidal.fieldUnitaryLatticeEquiv_generator
    f.toRingEquiv (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) b

@[simp]
theorem unitaryLatticeEquiv_coefficient (x : UnitaryLattice.{uE, uV} E)
    (b : UnitaryBasis.{uE, uV} E) :
    unitaryLatticeEquiv F E f x (unitaryBasisEquiv F E f b) = x b := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  exact Supercuspidal.fieldUnitaryLatticeEquiv_coefficient
    f.toRingEquiv (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) x b

theorem unitaryLatticeEquiv_symm :
    (unitaryLatticeEquiv.{uF, uE, uV} F E f).symm = unitaryLatticeEquiv E F f.symm := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  exact Supercuspidal.fieldUnitaryLatticeEquiv_symm
    f.toRingEquiv (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm)

/-- The inclusion of unitary lattices intertwines the two pullbacks. -/
@[simp]
theorem includeUnitary_unitaryLatticeEquiv (x : UnitaryLattice.{uE, uV} E) :
    includeUnitary F (unitaryLatticeEquiv F E f x) = latticeEquiv F E f (includeUnitary E x) := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  exact Supercuspidal.includeUnitary_fieldUnitaryLatticeEquiv
    f.toRingEquiv (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) x

@[simp]
theorem degree_latticeEquiv (x : Lattice.{uE, uV} E) :
    degree F (latticeEquiv F E f x) = degree E x := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  exact Supercuspidal.degree_fieldLatticeEquiv
    f.toRingEquiv (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) x

@[simp]
theorem unitaryDegree_unitaryLatticeEquiv (x : UnitaryLattice.{uE, uV} E) :
    unitaryDegree F (unitaryLatticeEquiv F E f x) = unitaryDegree E x := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  exact Supercuspidal.unitaryDegree_fieldUnitaryLatticeEquiv
    f.toRingEquiv (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) x

theorem unitaryPairing_unitaryLatticeEquiv (x y : UnitaryLattice.{uE, uV} E) :
    unitaryPairing F (unitaryLatticeEquiv F E f x) (unitaryLatticeEquiv F E f y) =
      unitaryPairing E x y := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  exact Supercuspidal.unitaryPairing_fieldUnitaryLatticeEquiv
    f.toRingEquiv (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) x y

end Langlands.VirtualRepresentation.PadicSupercuspidal
