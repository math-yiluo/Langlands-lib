import Langlands.AlgebraicGeometry.StalkEssFinitePresentationStatement
import Langlands.Algebra.EssFinitePresentationTransportProof

/-! # Essential finite presentation of scheme stalk maps -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- The local-ring map of a finitely presented ring homomorphism is essentially
finitely presented for the algebra structure induced by that map. -/
private theorem localRingHom_essFinitePresentation
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FinitePresentation) (q : Ideal S) [q.IsPrime] :
    let := (Localization.localRingHom _ q f rfl).toAlgebra
    Langlands.Algebra.EssFinitePresentation
      (Localization.AtPrime (q.comap f)) (Localization.AtPrime q) := by
  let M := (q.comap f).primeCompl
  let N := q.primeCompl
  have hMN : M.map f ≤ N := by
    rintro _ ⟨r, hr, rfl⟩
    exact hr
  let A := Localization (M.map f)
  let R' := Localization.AtPrime (q.comap f)
  let B := Localization.AtPrime q
  let : Algebra A B := IsLocalization.localizationAlgebraOfSubmonoidLe A B (M.map f) N hMN
  have : IsScalarTower S A B :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A B (M.map f) N hMN
  have : IsLocalization (N.map (algebraMap S A)) B :=
    IsLocalization.isLocalization_of_submonoid_le A B (M.map f) N hMN
  let g : R' →+* A := IsLocalization.map A f M.le_comap_map
  have hg : g.FinitePresentation :=
    RingHom.finitePresentation_localizationPreserves f M R' A hf
  let : Algebra R' A := g.toAlgebra
  have : Algebra.FinitePresentation R' A := hg
  let : Algebra R' B := (Localization.localRingHom _ q f rfl).toAlgebra
  have : IsScalarTower R' A B := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext M
    ext r
    change (Localization.localRingHom _ q f rfl)
        (algebraMap R (Localization.AtPrime (q.comap f)) r) =
      algebraMap A B (g (algebraMap R R' r))
    rw [Localization.localRingHom_to_map]
    change algebraMap S B (f r) =
      algebraMap A B (IsLocalization.map A f M.le_comap_map (algebraMap R R' r))
    rw [IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply S A B])
  exact Langlands.Algebra.essFinitePresentation_of_isLocalization R' A B (N.map (algebraMap S A))

/-- A locally finitely presented scheme morphism induces essential finite
presentation on its actual stalk maps. -/
theorem stalkEssFinitePresentation : StalkEssFinitePresentationStatement.{u} := by
  intro X Y f x hf
  exact HasRingHomProperty.stalkMap_of_respectsIso
    Langlands.Algebra.essFinitePresentation_respectsIso
    (fun g hg q _ => localRingHom_essFinitePresentation g hg q) hf x

example : StalkEssFinitePresentationStatement.{u} := @stalkEssFinitePresentation.{u}

end Langlands.AlgebraicGeometry
