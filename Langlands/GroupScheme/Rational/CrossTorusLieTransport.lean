import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Actual Lie weights and roots under transport between acting tori -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

namespace Lie

variable (f : G ≅ H) (A : Type u) [CommRing A] [Algebra R A]

@[simp] theorem targetMapLinear_hom_inv (x : Additive (lieKernel G A)) :
    targetMapLinear f.inv A (targetMapLinear f.hom A x) = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [lieKernelHomLinear_val, Category.assoc, ← Grp.comp_hom_hom,
    Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

@[simp] theorem targetMapLinear_inv_hom (x : Additive (lieKernel H A)) :
    targetMapLinear f.hom A (targetMapLinear f.inv A x) = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [lieKernelHomLinear_val, Category.assoc, ← Grp.comp_hom_hom,
    Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- An actual ambient group isomorphism induces a linear equivalence of the
actual dual-number identity kernels over every test algebra. -/
def targetEquiv : Additive (lieKernel G A) ≃ₗ[A] Additive (lieKernel H A) where
  toLinearMap := targetMapLinear f.hom A
  invFun := targetMapLinear f.inv A
  left_inv := targetMapLinear_hom_inv f A
  right_inv := targetMapLinear_inv_hom f A

@[simp] theorem targetEquiv_apply (x : Additive (lieKernel G A)) :
    targetEquiv f A x = targetMapLinear f.hom A x := rfl

@[simp] theorem targetEquiv_symm_apply (x : Additive (lieKernel H A)) :
    (targetEquiv f A).symm x = targetMapLinear f.inv A x := rfl

end Lie

variable {S S' : CommGroupScheme (Spec R)}

/-- Pulling back the acting group and character together preserves every actual
Lie weight, including its tests over all coefficient algebras. -/
theorem mem_weightSpace_precomp_torus_hom (i : S.toGrp ⟶ G)
    (a : characterLattice S) (τ : S' ⟶ S) {x : Additive (lieKernel G R)}
    (hx : x ∈ weightSpace i a) :
    x ∈ weightSpace (CommGroupScheme.groupHom τ ≫ i) (τ ≫ a) := by
  intro A _ _ t
  simpa only [Lie.characterValue_comp, Grp.comp_hom_hom, Category.assoc] using
    hx A (t ≫ (CommGroupScheme.groupHom τ).hom.hom)

variable {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
private theorem inverse_square (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    j ≫ f.inv = CommGroupScheme.groupHom e.inv ≫ i := by
  rw [Iso.comp_inv_eq, Category.assoc, h, ← Category.assoc]
  change j = CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ j
  rw [Iso.inv_hom_id]
  exact (Category.id_comp _).symm

/-- A commuting square transports the actual weight to inverse-precomposition
of its character, using the published linear differential on the ambient group. -/
theorem lieKernelHomLinear_mem_weightSpace_of_transport (e : S ≅ S') (f : G ⟶ H)
    (h : i ≫ f = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) {x : Additive (lieKernel G R)}
    (hx : x ∈ weightSpace i a) :
    Lie.targetMapLinear f R x ∈ weightSpace j (characterLattice.congr e a) := by
  have hc : CommGroupScheme.groupHom e.inv ≫ (i ≫ f) = j := by
    rw [h, ← Category.assoc]
    change CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ j = j
    rw [Iso.inv_hom_id]
    exact Category.id_comp _
  have hm := mem_weightSpace_precomp_torus_hom (i ≫ f) a e.inv
    (lieKernelHomLinear_mem_weightSpace f i a hx)
  rwa [hc] at hm

/-- The supplied ambient isomorphism preserves and reflects actual weight membership. -/
theorem lieKernelHomLinear_mem_weightSpace_transport_iff (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (x : Additive (lieKernel G R)) :
    Lie.targetMapLinear f.hom R x ∈ weightSpace j (characterLattice.congr e a) ↔
      x ∈ weightSpace i a := by
  constructor
  · intro hx
    have hm := lieKernelHomLinear_mem_weightSpace_of_transport e.symm f.inv
      (inverse_square e f h) (characterLattice.congr e a) hx
    simpa only [Lie.targetMapLinear_hom_inv, characterLattice.congr_apply,
      Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc] using hm
  · exact lieKernelHomLinear_mem_weightSpace_of_transport e f.hom h a

/-- Equality of actual weight submodules under the given differential. -/
theorem weightSpace_map_of_transport (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) (a : characterLattice S) :
    (weightSpace i a).map (Lie.targetMapLinear f.hom R) =
      weightSpace j (characterLattice.congr e a) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact lieKernelHomLinear_mem_weightSpace_of_transport e f.hom h a hx
  · intro hy
    refine ⟨Lie.targetMapLinear f.inv R y, ?_, Lie.targetMapLinear_inv_hom f R y⟩
    apply (lieKernelHomLinear_mem_weightSpace_transport_iff e f h a _).mp
    simpa only [Lie.targetMapLinear_inv_hom] using hy

/-- Linear equivalence of the full actual character weight spaces. -/
def weightSpaceTransportEquiv (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) (a : characterLattice S) :
    weightSpace i a ≃ₗ[R] weightSpace j (characterLattice.congr e a) where
  toFun x := ⟨Lie.targetMapLinear f.hom R x.val,
    lieKernelHomLinear_mem_weightSpace_of_transport e f.hom h a x.property⟩
  invFun y := ⟨Lie.targetMapLinear f.inv R y.val, by
    apply (lieKernelHomLinear_mem_weightSpace_transport_iff e f h a _).mp
    simpa only [Lie.targetMapLinear_inv_hom] using y.property⟩
  left_inv x := Subtype.ext (Lie.targetMapLinear_hom_inv f R x.val)
  right_inv y := Subtype.ext (Lie.targetMapLinear_inv_hom f R y.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

@[simp] theorem weightSpaceTransportEquiv_apply (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) (a : characterLattice S)
    (x : weightSpace i a) :
    (weightSpaceTransportEquiv e f h a x : Additive (lieKernel H R)) =
      Lie.targetMapLinear f.hom R x.val := rfl

@[simp] theorem weightSpaceTransportEquiv_symm_apply (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) (a : characterLattice S)
    (y : weightSpace j (characterLattice.congr e a)) :
    ((weightSpaceTransportEquiv e f h a).symm y : Additive (lieKernel G R)) =
      Lie.targetMapLinear f.inv R y.val := rfl

/-- Actual roots are preserved and reflected, with no splitness or reducedness assumption. -/
theorem roots_mem_of_transport_iff (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) (a : characterLattice S) :
    characterLattice.congr e a ∈ roots j ↔ a ∈ roots i := by
  have hn : characterLattice.congr e a = 0 ↔ a = 0 := by
    rw [← (characterLattice.congr e).map_zero]
    exact (characterLattice.congr e).injective.eq_iff
  have hw : weightSpace j (characterLattice.congr e a) = ⊥ ↔ weightSpace i a = ⊥ := by
    rw [← weightSpace_map_of_transport e f h a]
    exact Submodule.map_eq_bot_iff (e := Lie.targetEquiv f R)
  exact and_congr (not_congr hn) (not_congr hw)

/-- Equality of the actual character-valued root sets. -/
theorem roots_image_of_transport (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    characterLattice.congr e '' roots i = roots j := by
  ext a'
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (roots_mem_of_transport_iff e f h a).mpr ha
  · intro ha
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a'
    exact ⟨a, (roots_mem_of_transport_iff e f h a).mp ha, rfl⟩

/-- A bijection of actual roots restricting precisely the supplied character congruence. -/
def rootsTransportEquiv (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) : roots i ≃ roots j :=
  (characterLattice.congr e).toEquiv.subtypeEquiv (fun a => (roots_mem_of_transport_iff e f h a).symm)

@[simp] theorem rootsTransportEquiv_apply (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) (a : roots i) :
    (rootsTransportEquiv e f h a : characterLattice S') = characterLattice.congr e a := rfl

section Transporter

variable {j' : S'.toGrp ⟶ G}

/-- The weight equivalence for the same actual point appearing in the transporter square. -/
def weightSpaceTransporterEquiv (e : S ≅ S') (g : Over.mk (𝟙 (Spec R)) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j')
    (a : characterLattice S) :
    weightSpace i a ≃ₗ[R] weightSpace j' (characterLattice.congr e a) :=
  weightSpaceTransportEquiv e (G.innerIso g) h a

@[simp] theorem weightSpaceTransporterEquiv_apply_val (e : S ≅ S')
    (g : Over.mk (𝟙 (Spec R)) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j')
    (a : characterLattice S) (x : weightSpace i a) :
    (weightSpaceTransporterEquiv e g h a x).val.toMul.val =
      G.constantPoint g _ * x.val.toMul.val * (G.constantPoint g _)⁻¹ :=
  comp_innerIso_hom G g _ x.val.toMul.val

@[simp] theorem weightSpaceTransporterEquiv_symm_apply_val (e : S ≅ S')
    (g : Over.mk (𝟙 (Spec R)) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j')
    (a : characterLattice S) (x : weightSpace j' (characterLattice.congr e a)) :
    ((weightSpaceTransporterEquiv e g h a).symm x).val.toMul.val =
      (G.constantPoint g _)⁻¹ * x.val.toMul.val * G.constantPoint g _ := by
  change x.val.toMul.val ≫ (G.innerIso g).inv.hom.hom = _
  rw [← innerIso_inv_hom, comp_innerIso_hom, constantPoint_inv, inv_inv]

end Transporter

section Rational

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G₀ H₀ : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G₀.X.hom] [IsAffineHom H₀.X.hom]
  {i₀ : T.toGrp ⟶ G₀} {j₀ : T'.toGrp ⟶ H₀}

/-- The corresponding equality of actual relative-root sets over a field. -/
theorem relativeRoots_image_of_transport (e : T ≅ T') (f : G₀ ≅ H₀)
    (h : i₀ ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j₀) :
    characterLattice.congr e '' relativeRoots i₀ = relativeRoots j₀ :=
  roots_image_of_transport e f h

/-- The actual relative-root bijection; no reduced-root-system model is substituted. -/
def relativeRootsTransportEquiv (e : T ≅ T') (f : G₀ ≅ H₀)
    (h : i₀ ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j₀) :
    relativeRoots i₀ ≃ relativeRoots j₀ :=
  rootsTransportEquiv e f h

/-- Simultaneous transport of a character and cocharacter preserves positivity. -/
theorem positiveRelativeRoots_mem_of_transport_iff (e : T ≅ T') (f : G₀ ≅ H₀)
    (h : i₀ ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j₀)
    (ν : cocharacterLattice T) (a : characterLattice T) :
    characterLattice.congr e a ∈ positiveRelativeRoots j₀ (cocharacterLattice.congr e ν) ↔
      a ∈ positiveRelativeRoots i₀ ν := by
  change (_ ∈ roots j₀ ∧ 0 < _) ↔ (a ∈ roots i₀ ∧ 0 < _)
  rw [roots_mem_of_transport_iff e f h, latticePairing_congr]

/-- Indecomposability in the full positive relative roots is also preserved,
including when the relative root system is nonreduced. -/
theorem simpleRelativeRoots_mem_of_transport_iff (e : T ≅ T') (f : G₀ ≅ H₀)
    (h : i₀ ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j₀)
    (ν : cocharacterLattice T) (a : characterLattice T) :
    characterLattice.congr e a ∈ simpleRelativeRoots j₀ (cocharacterLattice.congr e ν) ↔
      a ∈ simpleRelativeRoots i₀ ν := by
  change (_ ∈ positiveRelativeRoots j₀ _ ∧ ¬ ∃ b ∈ positiveRelativeRoots j₀ _,
      ∃ c ∈ positiveRelativeRoots j₀ _, characterLattice.congr e a = b + c) ↔
    (a ∈ positiveRelativeRoots i₀ ν ∧ ¬ ∃ b ∈ positiveRelativeRoots i₀ ν,
      ∃ c ∈ positiveRelativeRoots i₀ ν, a = b + c)
  apply and_congr (positiveRelativeRoots_mem_of_transport_iff e f h ν a) (not_congr ?_)
  constructor
  · rintro ⟨b, hb, c, hc, ha⟩
    obtain ⟨b₀, rfl⟩ := (characterLattice.congr e).surjective b
    obtain ⟨c₀, rfl⟩ := (characterLattice.congr e).surjective c
    refine ⟨b₀, (positiveRelativeRoots_mem_of_transport_iff e f h ν b₀).mp hb,
      c₀, (positiveRelativeRoots_mem_of_transport_iff e f h ν c₀).mp hc, ?_⟩
    apply (characterLattice.congr e).injective
    simpa only [map_add] using ha
  · rintro ⟨b, hb, c, hc, ha⟩
    refine ⟨characterLattice.congr e b,
      (positiveRelativeRoots_mem_of_transport_iff e f h ν b).mpr hb,
      characterLattice.congr e c,
      (positiveRelativeRoots_mem_of_transport_iff e f h ν c).mpr hc, ?_⟩
    rw [ha, map_add]

/-- Generic cocharacters remain generic under the same actual torus identification. -/
theorem isGenericCocharacter_of_transport_iff (e : T ≅ T') (f : G₀ ≅ H₀)
    (h : i₀ ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j₀) (ν : cocharacterLattice T) :
    IsGenericCocharacter j₀ (cocharacterLattice.congr e ν) ↔ IsGenericCocharacter i₀ ν := by
  constructor
  · intro hν a ha
    have hn := hν (characterLattice.congr e a) ((roots_mem_of_transport_iff e f h a).mpr ha)
    rwa [latticePairing_congr] at hn
  · intro hν a' ha'
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a'
    rw [latticePairing_congr]
    exact hν a ((roots_mem_of_transport_iff e f h a).mp ha')

end Rational

end Langlands.GroupScheme
