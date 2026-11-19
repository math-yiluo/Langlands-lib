import Langlands.AlgebraicGeometry.Modules.StalkIsoLocus
import Langlands.AlgebraicGeometry.Modules.FiniteLocalBasisDescent
import Langlands.AlgebraicGeometry.Modules.RankOneStalkReflection
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Pullback reflects stalk isomorphisms between finite free stalks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Modules

/-- A linear map between finite free modules is bijective if its base change
along a local homomorphism to a nontrivial ring is bijective. -/
theorem bijective_of_bijective_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Nontrivial B]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
    (φ : M →ₗ[A] N) (h : Function.Bijective (φ.baseChange B)) : Function.Bijective φ := by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  let eB := LinearEquiv.ofBijective (φ.baseChange B) h
  have hrank : Module.finrank A M = Module.finrank A N := by
    have := eB.finrank_eq
    rwa [Module.finrank_baseChange, Module.finrank_baseChange] at this
  let e : N ≃ₗ[A] M := LinearEquiv.ofFinrankEq N M hrank.symm
  let ψ : Module.End A M := e.toLinearMap ∘ₗ φ
  have hψB : Function.Bijective (ψ.baseChange B) := by
    rw [LinearMap.baseChange_comp]
    exact (LinearEquiv.baseChange A B N M e).bijective.comp h
  have hunitB : IsUnit (ψ.baseChange B) := (Module.End.isUnit_iff _).mpr hψB
  rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_baseChange] at hunitB
  have hdet : IsUnit (LinearMap.det ψ) := (isUnit_map_iff (algebraMap A B) _).mp hunitB
  have hψ : Function.Bijective ψ :=
    (Module.End.isUnit_iff ψ).mp ((LinearMap.isUnit_iff_isUnit_det ψ).mpr hdet)
  have hφ : (φ : M → N) = e.symm ∘ ψ := by
    funext m
    simp [ψ]
  rw [hφ]
  exact e.symm.bijective.comp hψ


/-- Extension of scalars along a local homomorphism to a nontrivial ring reflects
isomorphisms between finite free modules. -/
theorem isIso_of_isIso_extendScalars_map {A B : CommRingCat.{u}} (g : A ⟶ B)
    [IsLocalHom g.hom] [Nontrivial B] {M N : ModuleCat.{u} A}
    [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
    (l : M ⟶ N) (h : IsIso ((ModuleCat.extendScalars g.hom).map l)) : IsIso l := by
  let : Algebra A B := ((algebraMap B B).comp g.hom).toAlgebra
  have : IsLocalHom (algebraMap A B) := by
    change IsLocalHom ((RingHom.id B).comp g.hom)
    infer_instance
  rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
  exact bijective_of_bijective_baseChange (B := B) l.hom h

variable {X Y : Scheme.{u}}

/-- Pullback along any morphism detects bijectivity of a stalk map at the image
point, when both stalks there are finite free. -/
theorem mem_isoLocus_pullback_iff_of_free (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N)
    (x : X) [Module.Free (Y.presheaf.stalk (f x)) (stalk M (f x))]
    [Module.Finite (Y.presheaf.stalk (f x)) (stalk M (f x))]
    [Module.Free (Y.presheaf.stalk (f x)) (stalk N (f x))]
    [Module.Finite (Y.presheaf.stalk (f x)) (stalk N (f x))] :
    x ∈ isoLocus ((Scheme.Modules.pullback f).map φ) ↔ f x ∈ isoLocus φ := by
  change Function.Bijective _ ↔ Function.Bijective _
  rw [bijective_stalkMap_iff_isIso_stalkFunctor_map,
    bijective_stalkMap_iff_isIso_stalkFunctor_map]
  refine (NatIso.isIso_map_iff (StalkPullback.pullbackStalkIso f x) φ).trans ?_
  constructor
  · intro h
    have : Module.Free (Y.presheaf.stalk (f x)) ((stalkFunctor (f x)).obj M) :=
      ‹Module.Free _ (stalk M (f x))›
    have : Module.Finite (Y.presheaf.stalk (f x)) ((stalkFunctor (f x)).obj M) :=
      ‹Module.Finite _ (stalk M (f x))›
    have : Module.Free (Y.presheaf.stalk (f x)) ((stalkFunctor (f x)).obj N) :=
      ‹Module.Free _ (stalk N (f x))›
    have : Module.Finite (Y.presheaf.stalk (f x)) ((stalkFunctor (f x)).obj N) :=
      ‹Module.Finite _ (stalk N (f x))›
    exact isIso_of_isIso_extendScalars_map (f.stalkMap x) ((stalkFunctor (f x)).map φ) h
  · intro h
    exact Functor.map_isIso (ModuleCat.extendScalars (f.stalkMap x).hom)
      ((stalkFunctor (f x)).map φ)

/-- Finite local bases make every stalk finite free over the local ring. -/
theorem free_stalk_of_hasFiniteLocalBasis (M : X.Modules)
    (h : Langlands.Scheme.Modules.HasFiniteLocalBasis M) (x : X) :
    Module.Free (X.presheaf.stalk x) (stalk M x) ∧
      Module.Finite (X.presheaf.stalk x) (stalk M x) := by
  have := isFinitePresentation_of_hasFiniteLocalBasis M h
  have := finitePresentation_stalk M x
  have := flat_stalk_of_hasFiniteLocalBasis M h x
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

/-- Pullback along any morphism detects bijectivity of a stalk map at the image
point, for a morphism between modules with finite local bases. -/
theorem mem_isoLocus_pullback_iff_of_hasFiniteLocalBasis (f : X ⟶ Y) {M N : Y.Modules}
    (hM : Langlands.Scheme.Modules.HasFiniteLocalBasis M)
    (hN : Langlands.Scheme.Modules.HasFiniteLocalBasis N) (φ : M ⟶ N) (x : X) :
    x ∈ isoLocus ((Scheme.Modules.pullback f).map φ) ↔ f x ∈ isoLocus φ := by
  obtain ⟨_, _⟩ := free_stalk_of_hasFiniteLocalBasis M hM (f x)
  obtain ⟨_, _⟩ := free_stalk_of_hasFiniteLocalBasis N hN (f x)
  exact mem_isoLocus_pullback_iff_of_free f φ x

end Langlands.AlgebraicGeometry.Modules
