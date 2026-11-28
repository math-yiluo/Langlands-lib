import Langlands.AlgebraicGeometry.AffineCechDeRhamInfinitesimalMorphism
import Langlands.AlgebraicGeometry.TwistedOpenGluingLift

/-! # Scheme transitions of affine endomorphisms with identity reduction -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

private abbrev sections (W : X.Opens) := (sectionAlgebras f).obj (op W)
private abbrev ringMap {W : X.Opens} (a : sections (f := f) W →ₐ[R] sections (f := f) W) :
    Γ(X, W) ⟶ Γ(X, W) := CommRingCat.ofHom a.toRingHom
private abbrev scalarMap (W : X.Opens) : CommRingCat.of R ⟶ Γ(X, W) :=
  CommRingCat.ofHom (algebraMap R (sections (f := f) W))

/-- Interpret an algebra endomorphism as a map of the actual affine open. -/
def affineOpenEndomorphism {W : X.Opens} (hW : IsAffineOpen W)
    (a : sections (f := f) W →ₐ[R] sections (f := f) W) : W.toScheme ⟶ W.toScheme :=
  hW.isoSpec.hom ≫ Spec.map (ringMap (f := f) (W := W) a) ≫ hW.isoSpec.inv

@[reassoc]
lemma affineOpenEndomorphism_isoSpec {W : X.Opens} (hW : IsAffineOpen W)
    (a : sections (f := f) W →ₐ[R] sections (f := f) W) :
    affineOpenEndomorphism hW a ≫ hW.isoSpec.hom =
      hW.isoSpec.hom ≫ Spec.map (ringMap (f := f) (W := W) a) := by
  rw [affineOpenEndomorphism, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[simp]
lemma affineOpenEndomorphism_id {W : X.Opens} (hW : IsAffineOpen W) :
    affineOpenEndomorphism hW (AlgHom.id R (sections (f := f) W)) = 𝟙 W.toScheme := by
  rw [← cancel_mono hW.isoSpec.hom, affineOpenEndomorphism_isoSpec, Category.id_comp]
  change hW.isoSpec.hom ≫ Spec.map (𝟙 Γ(X, W)) = hW.isoSpec.hom
  rw [Spec.map_id, Category.comp_id]

lemma affineOpenEndomorphism_comp {W : X.Opens} (hW : IsAffineOpen W)
    (a b : sections (f := f) W →ₐ[R] sections (f := f) W) :
    affineOpenEndomorphism hW a ≫ affineOpenEndomorphism hW b =
      affineOpenEndomorphism hW (a.comp b) := by
  rw [← cancel_mono hW.isoSpec.hom, Category.assoc, affineOpenEndomorphism_isoSpec,
    affineOpenEndomorphism_isoSpec_assoc, affineOpenEndomorphism_isoSpec,
    cancel_epi hW.isoSpec.hom, ← Spec.map_comp]
  rfl

@[reassoc]
private lemma homOfLE_isoSpec {W V : X.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (d : W ≤ V) :
    X.homOfLE d ≫ hV.isoSpec.hom =
      hW.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE d).op) := by
  apply (cancel_mono hV.fromSpec).mp
  rw [Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, Scheme.homOfLE_ι,
    Category.assoc, hV.map_fromSpec hW, IsAffineOpen.isoSpec_hom_fromSpec]

/-- Restriction of section rings intertwines the affine endomorphisms. -/
lemma affineOpenEndomorphism_homOfLE {W V : X.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (d : W ≤ V) (a : sections (f := f) V →ₐ[R] sections (f := f) V)
    (b : sections (f := f) W →ₐ[R] sections (f := f) W)
    (he : let ρ := ((sectionAlgebras f).map (homOfLE d).op).hom
      ρ.comp a = b.comp ρ) :
    affineOpenEndomorphism hW b ≫ X.homOfLE d = X.homOfLE d ≫ affineOpenEndomorphism hV a := by
  have he' : ringMap (f := f) (W := V) a ≫ X.presheaf.map (homOfLE d).op =
      X.presheaf.map (homOfLE d).op ≫ ringMap (f := f) (W := W) b := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun he x
  rw [← cancel_mono hV.isoSpec.hom, Category.assoc, Category.assoc,
    homOfLE_isoSpec hW hV d, affineOpenEndomorphism_isoSpec_assoc, affineOpenEndomorphism_isoSpec,
    homOfLE_isoSpec_assoc hW hV d, cancel_epi hW.isoSpec.hom,
    ← Spec.map_comp, ← Spec.map_comp, he']

private lemma fromSpec_over {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ f = Spec.map (scalarMap (f := f) W) := by
  let T : (Spec (CommRingCat.of R)).Opens := ⊤
  change hW.fromSpec ≫ f =
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE T W le_top)
  rw [Spec.map_comp]
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hW (U := T) le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  exact h.symm

lemma affineOpenEndomorphism_over {W : X.Opens} (hW : IsAffineOpen W)
    (a : sections (f := f) W →ₐ[R] sections (f := f) W) :
    affineOpenEndomorphism hW a ≫ W.ι ≫ f = W.ι ≫ f := by
  rw [affineOpenEndomorphism, Category.assoc, Category.assoc, ← Category.assoc hW.isoSpec.inv,
    IsAffineOpen.isoSpec_inv_ι, fromSpec_over (f := f) hW, ← Spec.map_comp]
  have ha : scalarMap (f := f) W ≫ ringMap (f := f) (W := W) a = scalarMap (f := f) W :=
    ConcreteCategory.hom_ext _ _ a.commutes
  rw [ha, ← fromSpec_over hW, IsAffineOpen.isoSpec_hom_fromSpec_assoc]

variable (I : Ideal R)

private lemma resReduction_isoSpec {W : X.Opens} (hW : IsAffineOpen W) :
    let r := quotientReductionMap f I
    let W₀ := r ⁻¹ᵁ W
    r.resLE W W₀ le_rfl ≫ hW.isoSpec.hom =
      (hW.preimage r).isoSpec.hom ≫ Spec.map (r.appLE W W₀ le_rfl) := by
  dsimp only
  rw [← cancel_mono hW.fromSpec, Category.assoc, Category.assoc,
    IsAffineOpen.isoSpec_hom_fromSpec, Scheme.Hom.resLE_comp_ι]
  rw [IsAffineOpen.SpecMap_appLE_fromSpec (quotientReductionMap f I)
    hW (hW.preimage (quotientReductionMap f I)), IsAffineOpen.isoSpec_hom_fromSpec_assoc]

/-- An affine endomorphism congruent to the identity agrees with it on
the actual preimage in the quotient of the base. -/
lemma affineOpenEndomorphism_reduction {W : X.Opens} (hW : IsAffineOpen W)
    (a : sections (f := f) W →ₐ[R] sections (f := f) W)
    (ha : ∀ x, a x - x ∈ I.map (algebraMap R (sections (f := f) W))) :
    let r := quotientReductionMap f I
    let W₀ := r ⁻¹ᵁ W
    r.resLE W W₀ le_rfl ≫ affineOpenEndomorphism hW a = r.resLE W W₀ le_rfl := by
  dsimp only
  let r := quotientReductionMap f I
  let W₀ := r ⁻¹ᵁ W
  have hs : ringMap (f := f) (W := W) a ≫ r.appLE W W₀ le_rfl = r.appLE W W₀ le_rfl := by
    apply ConcreteCategory.hom_ext
    intro x
    have hx := ha x
    rw [← (quotientReductionMap_appLE f I W hW).2,
      RingHom.mem_ker, map_sub, sub_eq_zero] at hx
    exact hx
  rw [← cancel_mono hW.isoSpec.hom, Category.assoc, affineOpenEndomorphism_isoSpec,
    ← Category.assoc, resReduction_isoSpec, Category.assoc, ← Spec.map_comp, hs]

open Langlands.AlgebraicGeometry.TwistedOpenGluing

/-- The affine endomorphism, followed by the open inclusion, fixes every
point if it has identity reduction along a square-zero quotient. -/
lemma affineOpenEndomorphism_pointwise (hI : I * I = ⊥) {W : X.Opens} (hW : IsAffineOpen W)
    (a : sections (f := f) W →ₐ[R] sections (f := f) W)
    (ha : ∀ x, a x - x ∈ I.map (algebraMap R (sections (f := f) W))) :
    IsPointwiseInclusion (affineOpenEndomorphism hW a ≫ W.ι) := by
  let r := quotientReductionMap f I
  let : Surjective r := quotientReductionMap_surjective f I hI
  intro x
  obtain ⟨z, hz⟩ := r.surjective x.val
  let W₀ := r ⁻¹ᵁ W
  let z' : W₀.toScheme := ⟨z, by change r z ∈ W; rw [hz]; exact x.property⟩
  have hz' : r.resLE W W₀ le_rfl z' = x :=
    Subtype.ext ((Scheme.Hom.coe_resLE_apply r le_rfl z').trans hz)
  have hh := affineOpenEndomorphism_reduction I hW a ha
  rw [← hz', Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (r.resLE W W₀ le_rfl), hh]

end Langlands.AlgebraicGeometry.AffineCechDeRham
