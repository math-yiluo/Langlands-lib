import Langlands.GroupScheme.Descent.TensorComponents

/-! # Overlap components for commutative ring tensor decompositions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Descent.RingTensor

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {I : Type}

/-- The actual map of spectra associated to the given algebra. -/
abbrev map (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- A coordinate of the ring tensor equivalence as an actual overlap map. -/
def component (e : (S ⊗[R] S) ≃ₐ[S] (I → S)) (i : I) :
    Spec (CommRingCat.of S) ⟶ Overlap (map R S) :=
  Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ : I => S) i).comp e.toRingHom)) ≫
    (pullbackSpecIso R S S).inv

/-- These components form the actual finite coproduct decomposition. -/
instance component_isIso_desc [Finite I] (e : (S ⊗[R] S) ≃ₐ[S] (I → S)) :
    IsIso (Sigma.desc (component e)) := by
  have : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
    isIso_SpecMap_iff.mpr e.bijective
  have : IsIso (sigmaSpec (fun _ : I => CommRingCat.of S)) := finiteSigmaSpec_isIso _
  have h : Sigma.desc (component e) =
      sigmaSpec (fun _ : I => CommRingCat.of S) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ (pullbackSpecIso R S S).inv := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, ι_sigmaSpec_assoc, component]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [h]
  infer_instance

@[reassoc (attr := simp)]
theorem component_fst (e : (S ⊗[R] S) ≃ₐ[S] (I → S)) (i : I) :
    component e i ≫ fst (map R S) = 𝟙 _ := by
  dsimp only [component, fst, map]
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change e (a ⊗ₜ[R] 1) i = a
  exact congrFun (e.commutes a) i

@[reassoc (attr := simp)]
theorem component_snd
    (e : (S ⊗[R] S) ≃ₐ[S] (I → S)) (s : I → S ≃ₐ[R] S)
    (he : ∀ a b i, e (a ⊗ₜ[R] b) i = a * s i b) (i : I) :
    component e i ≫ snd (map R S) =
      Spec.map (CommRingCat.ofHom (s i).toRingHom) := by
  dsimp only [component, snd, map]
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  change e (1 ⊗ₜ[R] b) i = s i b
  simp only [he, one_mul]

instance component_fst_isIso (e : (S ⊗[R] S) ≃ₐ[S] (I → S)) (i : I) :
    IsIso (component e i ≫ fst (map R S)) := by
  rw [component_fst]
  infer_instance

theorem component_snd_isIso
    (e : (S ⊗[R] S) ≃ₐ[S] (I → S)) (s : I → S ≃ₐ[R] S)
    (he : ∀ a b i, e (a ⊗ₜ[R] b) i = a * s i b) (i : I) :
    IsIso (component e i ≫ snd (map R S)) := by
  rw [component_snd e s he]
  exact isIso_SpecMap_iff.mpr (s i).bijective

end Langlands.GroupScheme.Descent.RingTensor
