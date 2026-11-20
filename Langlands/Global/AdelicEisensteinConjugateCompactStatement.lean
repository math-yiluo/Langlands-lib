import Langlands.Global.AdelicIntertwiningOperator

/-! # Eisenstein operators for conjugate Iwasawa compacts -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- Conjugating an Iwasawa compact and translating the argument on the right
transports the actual Eisenstein and intertwining formulas by height scalars. -/
def EisensteinConjugateCompactTransportStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (iU : U ⟶ P) (l : M ⟶ P)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left]
    (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (c : M' ⟶ M) (proj : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (K : Subgroup (AdelicGroupPoints F G)) (hP : IsIwasawaCompact p K) (hQ : IsIwasawaCompact q K)
    (t : AdelicGroupPoints F G),
    let K' := K.map (MulAut.conj t⁻¹).toMonoidHom
    ∃ (hP' : IsIwasawaCompact p K') (hQ' : IsIwasawaCompact q K'),
      ∀ (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
        (g : AdelicGroupPoints F G),
        hP'.eisensteinSeries φ lam (g * t) =
          hP'.heightPower lam t * hP.eisensteinSeries (fun x => φ (x * t)) lam g ∧
        hQ'.eisensteinSeries φ (weylParameter l c proj lam) (g * t) =
          hQ'.heightPower (weylParameter l c proj lam) t *
            hQ.eisensteinSeries (fun x => φ (x * t)) (weylParameter l c proj lam) g ∧
        hP'.intertwiningOperator hQ' iU l iV c proj w φ lam (g * t) =
          (hQ'.heightPower (-weylParameter l c proj lam) t * hP'.heightPower lam t) *
            hP.intertwiningOperator hQ iU l iV c proj w (fun x => φ (x * t)) lam g

end Langlands.Global
