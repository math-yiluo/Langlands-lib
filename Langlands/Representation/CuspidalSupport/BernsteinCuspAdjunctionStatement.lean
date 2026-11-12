import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Smooth.FiniteLengthGrothendieck
import Langlands.Representation.Category.Abelian
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The functors `I : Cusp(G) → M(G)` and `R : M(G) → Cusp(G)` (Renard VI.7.2, second Lemma)

`Cusp(G)` is the product, over the standard parabolic subgroups `P = MN` of `G`, of the full
subcategories `M(M)_sc` of cuspidal smooth representations of the standard Levi subgroups.
`I` sends `(ρ_M)_P` to `⊕_P i_P^G(ρ_M)` and `R` sends `V` to `(r_P^G(V)_sc)_P`, where `W ↦ W_sc` is
the cuspidal part, a left adjoint of the inclusion `M(M)_sc → M(M)`. Then `R` is left adjoint to
`I`; `R` is exact, faithful and preserves representations of finite type; `I` is exact and
faithful; and every unit morphism `V → IR(V)` is injective.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.7.2, second Lemma, for the actual standard family, at the saturated carrier
universe `max uF uV`. For each finite set `J` of simple roots (the standard parabolic
`P_J = M_J N_J`), `M(M_J)_sc` is the full subcategory of smooth representations of the literal
standard Levi subgroup `M_J(F)` whose proper standard normalized Jacquet modules vanish
(`IsLeviCuspidal`), and `Cusp(G)` is the product of these categories. `I` sends `(ρ_J)_J` to the
coproduct of the normalized inductions `i_{P_J}^G(ρ_J)`. Then

* every inclusion `M(M_J)_sc → M(M_J)` has a left adjoint (a cuspidal-part functor
  `W ↦ W_sc`);
* for every choice `sc` of such left adjoints, the functor `R : V ↦ (r_{P_J}^G(V)_sc)_J`
  (normalized Jacquet module, then cuspidal part) satisfies:
  - (i) `R` is left adjoint to `I`;
  - (ii) `R` is faithful, exact (short exact sequences go to componentwise short exact
    sequences) and sends representations of finite type to objects all of whose components are
    of finite type; `I` is faithful and exact (componentwise short exact sequences go to short
    exact sequences);
  - (iii) for every adjunction `R ⊣ I`, every unit morphism `V → IR(V)` is injective. -/
def BernsteinCuspAdjunctionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν),
      haveI : Finite (SimpleRoot i ν) := family.finiteSimpleRoots
      let cusp : ∀ J : Finset (SimpleRoot i ν),
          ObjectProperty (SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) := fun J W =>
        Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
          family.closedUnipotent J (family.closedLevi J) (family.leviDecomposition J) W
      let jac : ∀ J : Finset (SimpleRoot i ν),
          SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
            SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) := fun J =>
        normalizedJacquetFunctor (unipotent i ν J) (levi i ν J) (family.closedUnipotent J)
          (family.decomposition J).levi_le_normalizer
      let Ifun : (∀ J : Finset (SimpleRoot i ν), (cusp J).FullSubcategory) ⥤
          SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
        Functor.pi (fun J => (cusp J).ι ⋙
            normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)) ⋙
          (piEquivalenceFunctorDiscrete (Finset (SimpleRoot i ν))
            (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))).functor ⋙ colim
      (∀ J : Finset (SimpleRoot i ν),
        ∃ sc : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) ⥤ (cusp J).FullSubcategory,
          Nonempty (sc ⊣ (cusp J).ι)) ∧
      ∀ sc : ∀ J : Finset (SimpleRoot i ν),
          SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) ⥤ (cusp J).FullSubcategory,
        (∀ J, Nonempty (sc J ⊣ (cusp J).ι)) →
        let R : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
            (∀ J : Finset (SimpleRoot i ν), (cusp J).FullSubcategory) :=
          Functor.pi' fun J => jac J ⋙ sc J
        Nonempty (R ⊣ Ifun) ∧
        (R.Faithful ∧
          (∀ {A B C : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)} (f : A ⟶ B) (g : B ⟶ C),
            SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g) →
              ∀ J, SmoothRep.IsShortExact (SmoothRep.hom ((R.map f) J).hom)
                (SmoothRep.hom ((R.map g) J).hom)) ∧
          (∀ V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
            Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) V.representation.asModule →
              ∀ J, Module.Finite (MonoidAlgebra ℂ (levi i ν J))
                ((R.obj V) J).obj.representation.asModule)) ∧
        (Ifun.Faithful ∧
          ∀ {X Y Z : ∀ J : Finset (SimpleRoot i ν), (cusp J).FullSubcategory}
            (f : X ⟶ Y) (g : Y ⟶ Z),
            (∀ J, SmoothRep.IsShortExact (SmoothRep.hom (f J).hom) (SmoothRep.hom (g J).hom)) →
              SmoothRep.IsShortExact (SmoothRep.hom (Ifun.map f)) (SmoothRep.hom (Ifun.map g))) ∧
        ∀ (adj : R ⊣ Ifun) (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
          Function.Injective (SmoothRep.hom (adj.unit.app V))

end Langlands.CuspidalSupport
