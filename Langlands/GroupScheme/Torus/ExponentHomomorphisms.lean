import Langlands.GroupScheme.Torus.ExponentCocharacters
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCharacters

/-! # Actual integral-coordinate torus morphisms over arbitrary schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

section Scheme

variable (S : Scheme.{u}) (I J K : Type u)
  [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

/-- Fixed-exponent characters depend integrally linearly on their coordinates,
over any scheme. -/
def exponentCharacterLinear : (I → ℤ) →ₗ[ℤ] characterLattice (commGroupScheme S I) where
  toFun := exponentCharacter S I
  map_add' m n := by
    simp only [exponentCharacter, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a m := by
    simp only [exponentCharacter, Pi.smul_apply, smul_eq_mul,
      Finset.smul_sum, smul_smul, RingHom.id_apply]

/-- An actual torus homomorphism from an integral map on character coordinates.
The integral map acts contravariantly. -/
def exponentHom (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) :
    commGroupScheme S I ⟶ commGroupScheme S J :=
  ∑ j, exponentCharacter S I (f (Pi.single j 1)) ≫ single S J j

omit [DecidableEq I] in
/-- Each target coordinate is exactly its specified exponent character. -/
@[simp] theorem exponentHom_comp_proj (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (j : J) :
    exponentHom S I J f ≫ proj S J j = exponentCharacter S I (f (Pi.single j 1)) := by
  simp only [exponentHom, Preadditive.sum_comp, Category.assoc, single_comp_proj]
  rw [Finset.sum_eq_single j]
  · simp
  · intro a _ haj
    simp [haj]
  · simp

omit [DecidableEq I] in
/-- The integral character pullback formula is an equality of actual maps
over the whole arbitrary base. -/
theorem exponentHom_comp_exponentCharacter
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (m : J → ℤ) :
    exponentHom S I J f ≫ exponentCharacter S J m = exponentCharacter S I (f m) := by
  have hm : ∑ j, m j • f (Pi.single j 1) = f m := by
    have hm0 : ∑ j, m j • (Pi.single j 1 : J → ℤ) = m := by
      ext j
      simp [Pi.single_apply]
    simpa only [map_sum, map_smul] using congrArg f hm0
  conv_lhs => rw [exponentCharacter]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, exponentHom_comp_proj]
  change ∑ j, m j • exponentCharacterLinear S I (f (Pi.single j 1)) =
    exponentCharacterLinear S I (f m)
  rw [← hm, map_sum]
  simp only [map_smul]

omit [DecidableEq J] in
/-- Maps to the standard torus agree if all their coordinate characters agree. -/
theorem hom_ext_projections {T : CommGroupScheme S}
    {f g : T ⟶ commGroupScheme S J}
    (h : ∀ j, f ≫ proj S J j = g ≫ proj S J j) : f = g := by
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = g ≫ 𝟙 _ := by
      rw [← sum_proj_comp_single S J]
      simp only [Preadditive.comp_sum, ← Category.assoc, h]
    _ = g := Category.comp_id _

omit [DecidableEq I] in
/-- Composition realizes composition of the contravariant integral maps. -/
@[simp] theorem exponentHom_comp
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (g : (K → ℤ) →ₗ[ℤ] (J → ℤ)) :
    exponentHom S I J f ≫ exponentHom S J K g = exponentHom S I K (f.comp g) := by
  apply hom_ext_projections S K
  intro a
  rw [Category.assoc, exponentHom_comp_proj, exponentHom_comp_exponentCharacter,
    exponentHom_comp_proj]
  rfl

/-- The identity integral map gives the actual identity torus map. -/
@[simp] theorem exponentHom_id :
    exponentHom S I I LinearMap.id = 𝟙 (commGroupScheme S I) := by
  apply hom_ext_projections S I
  intro j
  rw [exponentHom_comp_proj, Category.id_comp]
  simp [exponentCharacter, Pi.single_apply]

/-- Every integral coordinate automorphism gives an actual torus automorphism
over every base scheme. -/
def exponentCommIso (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :
    commGroupScheme S I ≅ commGroupScheme S I where
  hom := exponentHom S I I e.toLinearMap
  inv := exponentHom S I I e.symm.toLinearMap
  hom_inv_id := by
    rw [exponentHom_comp]
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext m
      simp
    rw [he, exponentHom_id]
  inv_hom_id := by
    rw [exponentHom_comp]
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext m
      simp
    rw [he, exponentHom_id]

/-- The same actual automorphism in the category of group schemes. -/
def exponentIso (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :
    splitTorus S I ≅ splitTorus S I where
  hom := CommGroupScheme.groupHom (exponentCommIso S I e).hom
  inv := CommGroupScheme.groupHom (exponentCommIso S I e).inv
  hom_inv_id := congrArg CommGroupScheme.groupHom (exponentCommIso S I e).hom_inv_id
  inv_hom_id := congrArg CommGroupScheme.groupHom (exponentCommIso S I e).inv_hom_id

/-- A specified inversion in the integral lattice is the actual character
inversion equation over the arbitrary base. -/
theorem exponentIso_inverts_character
    (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) (m : I → ℤ) (hm : e m = -m) :
    (exponentIso S I e).hom ≫ CommGroupScheme.groupHom (exponentCharacter S I m) =
      CommGroupScheme.groupHom (-exponentCharacter S I m) := by
  change CommGroupScheme.groupHom
    (exponentHom S I I e.toLinearMap ≫ exponentCharacter S I m) = _
  apply congrArg CommGroupScheme.groupHom
  rw [exponentHom_comp_exponentCharacter]
  change exponentCharacterLinear S I (e m) = -exponentCharacterLinear S I m
  rw [hm, map_neg]

variable {S' : Scheme.{u}} (b : S' ⟶ S)

omit [DecidableEq I] in
/-- Fixed integral-coordinate maps commute with arbitrary scheme base change,
through the canonical source and target torus identifications. -/
theorem exponentHom_baseChange (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) :
    (commBaseChangeIso b I).hom ≫ exponentHom S' I J f =
      (CommGroupScheme.baseChange b).map (exponentHom S I J f) ≫
        (commBaseChangeIso b J).hom := by
  apply hom_ext_projections S' J
  intro j
  rw [Category.assoc, exponentHom_comp_proj, Category.assoc,
    commBaseChangeIso_hom_proj, ← Functor.map_comp_assoc, exponentHom_comp_proj]
  exact exponentCharacter_baseChange S I b (f (Pi.single j 1))

/-- The group-scheme automorphisms from an integral coordinate equivalence
commute with arbitrary base change. -/
theorem exponentIso_baseChange (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :
    (baseChangeIso b I).hom ≫ (exponentIso S' I e).hom =
      (baseChange b).map (exponentIso S I e).hom ≫ (baseChangeIso b I).hom :=
  congrArg CommGroupScheme.groupHom (exponentHom_baseChange S I I b e.toLinearMap)

end Scheme

section Field

variable (k : Type u) [Field k] (I J K : Type u)
  [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

omit [DecidableEq I] in
/-- The fixed-coordinate extension of the actual integral character map
recovers every given actual field split-torus homomorphism. -/
theorem exponentHom_characterMap
    (q : splitTorus (Spec (CommRingCat.of k)) I ⟶
      splitTorus (Spec (CommRingCat.of k)) J) :
    exponentHom (Spec (CommRingCat.of k)) I J (characterMap I J q) = Additive.ofMul q := by
  apply hom_ext_projections _ J
  intro j
  rw [exponentHom_comp_proj, exponentCharacter_eq_characterLatticeEquiv_symm]
  apply (characterLatticeEquiv k I).injective
  rw [AddEquiv.apply_symm_apply, ← characterLatticeEquiv_proj (k := k) J j, characterMap_equiv]

omit [DecidableEq I] [DecidableEq J] [DecidableEq K] in
/-- Pullback on integral coordinates respects actual composition. -/
theorem characterMap_comp
    (f : splitTorus (Spec (CommRingCat.of k)) I ⟶
      splitTorus (Spec (CommRingCat.of k)) J)
    (g : splitTorus (Spec (CommRingCat.of k)) J ⟶
      splitTorus (Spec (CommRingCat.of k)) K) :
    characterMap I K (f ≫ g) = (characterMap I J f).comp (characterMap J K g) := by
  apply LinearMap.ext
  intro m
  obtain ⟨χ, rfl⟩ := (characterLatticeEquiv k K).surjective m
  rw [characterMap_equiv, LinearMap.comp_apply, characterMap_equiv, characterMap_equiv]
  rfl

omit [DecidableEq I] in
@[simp] theorem characterMap_id :
    characterMap I I (𝟙 (splitTorus (Spec (CommRingCat.of k)) I)) = LinearMap.id := by
  apply LinearMap.ext
  intro m
  obtain ⟨χ, rfl⟩ := (characterLatticeEquiv k I).surjective m
  rw [characterMap_equiv]
  change characterLatticeEquiv k I (𝟙 (commGroupScheme _ I) ≫ χ) = _
  rw [Category.id_comp]
  rfl

/-- The actual coordinate character action of a specified field torus
automorphism, as an integral linear equivalence. -/
def characterCoordinateIso
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) I) :
    (I → ℤ) ≃ₗ[ℤ] (I → ℤ) :=
  LinearEquiv.ofLinearMap (characterMap I I c.hom) (characterMap I I c.inv)
    (by rw [← characterMap_comp, c.hom_inv_id, characterMap_id])
    (by rw [← characterMap_comp, c.inv_hom_id, characterMap_id])

/-- Every actual field torus automorphism extends, with its fixed integral
coordinates, over any base scheme. -/
def fieldAutomorphismExtension (S : Scheme.{u})
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) I) :
    splitTorus S I ≅ splitTorus S I :=
  exponentIso S I (characterCoordinateIso k I c)

/-- Specializing the extension to its original field recovers the specified
actual field automorphism. -/
theorem fieldAutomorphismExtension_hom
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) I) :
    (fieldAutomorphismExtension k I (Spec (CommRingCat.of k)) c).hom = c.hom :=
  congrArg CommGroupScheme.groupHom (exponentHom_characterMap k I I c.hom)

/-- Pulling the relative extension back along any point with the original
field recovers the specified actual field automorphism. -/
theorem fieldAutomorphismExtension_baseChange (S : Scheme.{u})
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) I)
    (b : Spec (CommRingCat.of k) ⟶ S) :
    (baseChangeIso b I).inv ≫
        (baseChange b).map (fieldAutomorphismExtension k I S c).hom ≫
        (baseChangeIso b I).hom = c.hom := by
  change (baseChangeIso b I).inv ≫
    (baseChange b).map (exponentIso S I (characterCoordinateIso k I c)).hom ≫
    (baseChangeIso b I).hom = _
  rw [← exponentIso_baseChange, Iso.inv_hom_id_assoc]
  exact fieldAutomorphismExtension_hom k I c

/-- A specified actual field inversion remains the exact actual character
inversion over every base scheme under the integral-coordinate extension. -/
theorem fieldAutomorphismExtension_inverts_character (S : Scheme.{u})
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) I)
    (α : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (hα : c.hom ≫ CommGroupScheme.groupHom α = CommGroupScheme.groupHom (-α)) :
    (fieldAutomorphismExtension k I S c).hom ≫
        CommGroupScheme.groupHom (exponentCharacter S I (characterLatticeEquiv k I α)) =
      CommGroupScheme.groupHom
        (-exponentCharacter S I (characterLatticeEquiv k I α)) := by
  apply exponentIso_inverts_character
  change characterMap I I c.hom (characterLatticeEquiv k I α) =
    -characterLatticeEquiv k I α
  have hc : (Additive.ofMul c.hom : commGroupScheme _ I ⟶ commGroupScheme _ I) ≫ α = -α :=
    congrArg Additive.ofMul hα
  rw [characterMap_equiv]
  exact (congrArg (characterLatticeEquiv k I) hc).trans
    ((characterLatticeEquiv k I).map_neg α)

end Field

end Langlands.GroupScheme.splitTorus
