import Langlands.LocalFactor.CommonClosure
import Langlands.Weil.Local.ExtensionWeilEquiv

/-!
# Finite intermediate fields along an isomorphism of p-adic fields

For `g : F ≅ E` over `ℚ_p`, the chosen closure isomorphism `σ : F̄ ≅ Ē` over `g`
sends each finite intermediate field `L` of `F̄` to a finite intermediate field
`σ(L)` of `Ē`. We construct the field isomorphism `L ≅ σ(L)` over `ℚ_p` and the
isomorphism of fixing Weil subgroups `W_E(σ(L)) ≅ W_F(L)` given by the local
Weil map of `g`.
-/

noncomputable section

universe u₁ u₂

namespace Langlands.LocalFactor.NonabelianSystem.FieldTransport

open LocalClassField Weil.Local CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u₁} p) (E : PadicField.{u₂} p)
  (g : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- The chosen closure isomorphism `F̄ ≅ Ē` over `g`. -/
abbrev closureEquiv : AlgebraicClosure F.Carrier ≃+* AlgebraicClosure E.Carrier :=
  extensionClosureEquiv F E g.toAlgHom

theorem closureEquiv_algebraMap (x : F.Carrier) :
    closureEquiv F E g (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x) =
      algebraMap E.Carrier (AlgebraicClosure E.Carrier) (g x) :=
  extensionClosureLift_algebraMap F E g.toAlgHom x

theorem closureEquiv_symm_algebraMap (y : E.Carrier) :
    (closureEquiv F E g).symm (algebraMap E.Carrier (AlgebraicClosure E.Carrier) y) =
      algebraMap F.Carrier (AlgebraicClosure F.Carrier) (g.symm y) := by
  apply (closureEquiv F E g).injective
  rw [RingEquiv.apply_symm_apply, closureEquiv_algebraMap, AlgEquiv.apply_symm_apply]

/-- The image `σ(L)` of an intermediate field of `F̄`, an intermediate field of `Ē`. -/
def mapField (L : Extension F) : IntermediateField E.Carrier (AlgebraicClosure E.Carrier) :=
  (L.field.toSubfield.map (closureEquiv F E g).toRingHom).toIntermediateField (fun x =>
    ⟨algebraMap F.Carrier (AlgebraicClosure F.Carrier) (g.symm x),
      L.field.algebraMap_mem _, by
        change closureEquiv F E g _ = _
        rw [closureEquiv_algebraMap, AlgEquiv.apply_symm_apply]⟩)

theorem mem_mapField_iff (L : Extension F) (y : AlgebraicClosure E.Carrier) :
    y ∈ mapField F E g L ↔ (closureEquiv F E g).symm y ∈ L.field := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (closureEquiv F E g).symm (closureEquiv F E g x) ∈ L.field
    rwa [RingEquiv.symm_apply_apply]
  · intro hy
    exact ⟨_, hy, RingEquiv.apply_symm_apply _ y⟩

theorem apply_mem_mapField (L : Extension F) {x : AlgebraicClosure F.Carrier}
    (hx : x ∈ L.field) : closureEquiv F E g x ∈ mapField F E g L := by
  rw [mem_mapField_iff, RingEquiv.symm_apply_apply]
  exact hx

/-- The semilinear restriction `L → σ(L)` of the closure isomorphism. -/
def mapFieldSemilinear (L : Extension F) :
    L.field →ₛₗ[(g : F.Carrier →+* E.Carrier)] mapField F E g L where
  toFun x := ⟨closureEquiv F E g x, apply_mem_mapField F E g L x.2⟩
  map_add' x y := Subtype.ext (map_add (closureEquiv F E g) (x : AlgebraicClosure F.Carrier) y)
  map_smul' a x := by
    apply Subtype.ext
    show closureEquiv F E g ((a • x : L.field) : AlgebraicClosure F.Carrier) =
      ((g a • (⟨closureEquiv F E g x, apply_mem_mapField F E g L x.2⟩ : mapField F E g L) :
        mapField F E g L) : AlgebraicClosure E.Carrier)
    rw [IntermediateField.coe_smul, IntermediateField.coe_smul, Algebra.smul_def,
      Algebra.smul_def, map_mul, closureEquiv_algebraMap]

theorem mapFieldSemilinear_surjective (L : Extension F) :
    Function.Surjective (mapFieldSemilinear F E g L) := by
  rintro ⟨y, hy⟩
  exact ⟨⟨_, (mem_mapField_iff F E g L y).mp hy⟩,
    Subtype.ext (RingEquiv.apply_symm_apply _ y)⟩

instance mapField_finiteDimensional (L : Extension F) :
    FiniteDimensional E.Carrier (mapField F E g L) :=
  Module.Finite.of_surjective (mapFieldSemilinear F E g L)
    (mapFieldSemilinear_surjective F E g L)

/-- The finite intermediate field `σ(L)` of `Ē`. -/
def mapExtension (L : Extension F) : Extension E :=
  ⟨mapField F E g L, inferInstance⟩

@[simp] theorem mapExtension_field (L : Extension F) :
    (mapExtension F E g L).field = mapField F E g L := rfl

theorem mapExtension_mono {M L : Extension F} (h : M.field ≤ L.field) :
    (mapExtension F E g M).field ≤ (mapExtension F E g L).field := by
  intro y hy
  rw [mapExtension_field, mem_mapField_iff] at hy ⊢
  exact h hy

/-- The bottom field is sent to the bottom field. -/
theorem mapField_bot (L : Extension F) (hL : L.field = ⊥) :
    mapField F E g L = ⊥ := by
  ext y
  rw [mem_mapField_iff, hL, IntermediateField.mem_bot, IntermediateField.mem_bot]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨g x, ?_⟩
    rw [← closureEquiv_algebraMap, hx, RingEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    exact ⟨g.symm x, (closureEquiv_symm_algebraMap F E g x).symm⟩

/-! ## The field isomorphism `L ≅ σ(L)` over `ℚ_p` -/

/-- The restriction of the closure isomorphism to `L ≅ σ(L)`, as rings. -/
def mapFieldRingEquiv (L : Extension F) : L.field ≃+* (mapExtension F E g L).field where
  toFun x := ⟨closureEquiv F E g x, apply_mem_mapField F E g L x.2⟩
  invFun y := ⟨(closureEquiv F E g).symm y, (mem_mapField_iff F E g L y).mp y.2⟩
  left_inv _ := Subtype.ext (RingEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (RingEquiv.apply_symm_apply _ _)
  map_mul' x y := Subtype.ext (map_mul (closureEquiv F E g) (x : AlgebraicClosure F.Carrier) y)
  map_add' x y := Subtype.ext (map_add (closureEquiv F E g) (x : AlgebraicClosure F.Carrier) y)

/-- A ring isomorphism of p-adic fields commuting with the maps from `ℚ_p` is an
algebra isomorphism for their p-adic structures. -/
def padicAlgEquivOfRingEquiv (A : PadicField.{u₁} p) (B : PadicField.{u₂} p)
    (e : A.Carrier ≃+* B.Carrier)
    (he : ∀ r : Padic p, e (algebraMap (Padic p) A.Carrier r) = algebraMap (Padic p) B.Carrier r) :
    A.Carrier ≃ₐ[Padic p] B.Carrier :=
  { e with commutes' := he }

/-- The restriction of the closure isomorphism to `L ≅ σ(L)`, over `ℚ_p` for the
p-adic structures of `L.asPadicField` and `σ(L).asPadicField`. The type is left to
be inferred so that it carries the instances of these p-adic fields. -/
def fieldEquiv (L : Extension F) :=
  padicAlgEquivOfRingEquiv (L.asPadicField (p := p)) ((mapExtension F E g L).asPadicField (p := p))
    (mapFieldRingEquiv F E g L) (fun r => by
      apply Subtype.ext
      change closureEquiv F E g (algebraMap F.Carrier (AlgebraicClosure F.Carrier)
          (algebraMap (Padic p) F.Carrier r)) =
        algebraMap E.Carrier (AlgebraicClosure E.Carrier) (algebraMap (Padic p) E.Carrier r)
      rw [closureEquiv_algebraMap, AlgEquiv.commutes])

@[simp] theorem fieldEquiv_coe (L : Extension F) (x : L.field) :
    ((fieldEquiv F E g L x : (mapExtension F E g L).field) : AlgebraicClosure E.Carrier) =
      closureEquiv F E g x := rfl

@[simp] theorem mapFieldRingEquiv_symm_coe (L : Extension F) (y : (mapExtension F E g L).field) :
    (((mapFieldRingEquiv F E g L).symm y : L.field) : AlgebraicClosure F.Carrier) =
      (closureEquiv F E g).symm y := rfl

/-! ## Fixing Weil subgroups -/

/-- The local Weil map of `g`, `W_E ≅ W_F`. -/
abbrev weilEquiv : localWeilGroup E ≃ₜ* localWeilGroup F :=
  extensionWeilEquiv F E g

theorem galoisMap_mem_fixingSubgroup_iff (L : Extension F)
    (τ : Field.absoluteGaloisGroup E.Carrier) :
    extensionGaloisMap F E g.toAlgHom τ ∈ L.field.fixingSubgroup ↔
      τ ∈ (mapExtension F E g L).field.fixingSubgroup := by
  refine (IntermediateField.mem_fixingSubgroup_iff (K := L.field) _).trans
    (Iff.trans ?_ (IntermediateField.mem_fixingSubgroup_iff
      (K := (mapExtension F E g L).field) τ).symm)
  constructor
  · intro h y hy
    have hy' := (mem_mapField_iff F E g L y).mp hy
    have h1 := extensionClosureLift_galoisMap F E g.toAlgHom τ ((closureEquiv F E g).symm y)
    have h2 : AlgEquiv.toAlgHom (extensionGaloisMap F E g.toAlgHom τ)
        ((closureEquiv F E g).symm y) =
          (closureEquiv F E g).symm y := h _ hy'
    have h3 : extensionClosureLift F E g.toAlgHom ((closureEquiv F E g).symm y) = y :=
      RingEquiv.apply_symm_apply (closureEquiv F E g) y
    rw [h2, h3] at h1
    exact h1.symm
  · intro h x hx
    apply (closureEquiv F E g).injective
    have h1 := extensionClosureLift_galoisMap F E g.toAlgHom τ x
    have h2 : AlgEquiv.toAlgHom τ (closureEquiv F E g x) = closureEquiv F E g x :=
      h _ (apply_mem_mapField F E g L hx)
    exact h1.trans h2

theorem weilEquiv_mem_iff (L : Extension F) (w : localWeilGroup E) :
    weilEquiv F E g w ∈ weilSubgroup F L ↔ w ∈ weilSubgroup E (mapExtension F E g L) := by
  change localProjection F (extensionWeilMap F E g.toAlgHom w) ∈ L.field.fixingSubgroup ↔
    localProjection E w ∈ (mapExtension F E g L).field.fixingSubgroup
  rw [localProjection_extensionWeilMap]
  exact galoisMap_mem_fixingSubgroup_iff F E g L _

/-- The isomorphism of fixing Weil subgroups `W_E(σ(L)) ≅ W_F(L)`. -/
def subgroupWeilEquiv (L : Extension F) :
    weilSubgroup E (mapExtension F E g L) ≃ₜ* weilSubgroup F L where
  toFun w := ⟨weilEquiv F E g w, (weilEquiv_mem_iff F E g L w).mpr w.2⟩
  invFun w := ⟨(weilEquiv F E g).symm w, (weilEquiv_mem_iff F E g L _).mp (by
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact w.2)⟩
  left_inv w := Subtype.ext ((weilEquiv F E g).symm_apply_apply (w : localWeilGroup E))
  right_inv w := Subtype.ext ((weilEquiv F E g).apply_symm_apply (w : localWeilGroup F))
  map_mul' x y := Subtype.ext (map_mul (weilEquiv F E g) (x : localWeilGroup E) y)
  continuous_toFun := ((weilEquiv F E g).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((weilEquiv F E g).symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem subgroupWeilEquiv_coe (L : Extension F)
    (w : weilSubgroup E (mapExtension F E g L)) :
    ((subgroupWeilEquiv F E g L w : weilSubgroup F L) : localWeilGroup F) =
      weilEquiv F E g w := rfl

@[simp] theorem subgroupWeilEquiv_symm_coe (L : Extension F) (w : weilSubgroup F L) :
    (((subgroupWeilEquiv F E g L).symm w : weilSubgroup E (mapExtension F E g L)) :
      localWeilGroup E) = (weilEquiv F E g).symm w := rfl

end Langlands.LocalFactor.NonabelianSystem.FieldTransport
