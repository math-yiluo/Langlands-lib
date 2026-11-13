import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Reductive.Basic

/-!
# Split components of parabolic subgroups (Renard V.3.1 and V.3.2)

A split component of a rational parabolic `P` of a connected reductive group `G` is a maximal
split torus of the radical `R(P)` (Renard V.2.1). Its centralizer is a Levi factor `M` of `P`
whose split component it is; conversely `A_M` is a split component of `P`. The unipotent
radical acts transitively on the split components. Levi subgroups of `G` are the centralizers
of split tori `A` with `A = A_M`. `P` is minimal exactly when its split components are maximal
split tori of `G`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Renard V.3.1: let `j : P ⟶ G` be a rational parabolic of a connected reductive group,
`r : R ⟶ P` its radical, and `a : A ⟶ R` a split component of `P`, that is a maximal split
torus of `R` (Renard V.2.1). Then the centralizer `M = Z(G, A)` is represented by a rational
Levi factor `l : M ⟶ P`, and `A`, factored through `M`, is the split component of `M`. -/
def ParabolicSplitComponentLeviStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
        IsGeometricSolvableRadical r →
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ R),
          IsMaximalSplitTorus a →
          ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P) (aL : A.toGrp ⟶ L),
            IsRationalLeviSubgroup l ∧
              (torusCentralizer (a ≫ r ≫ j)).IsRepresentedBy (l ≫ j) ∧
              aL ≫ l = a ≫ r ∧ IsSplitComponent aL

/-- Renard V.3.1 ("le choix d'une composante déployée de `P` est donc équivalent au choix d'un
facteur de Levi"), the direction from Levi factors to split components: for a rational Levi
factor `l : M ⟶ P` of a rational parabolic with radical `r : R ⟶ P`, the split component
`A_M` of `M` factors through `R` as a maximal split torus of `R`, that is as a split component
of `P`. -/
def LeviSplitComponentRadicalStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
        IsGeometricSolvableRadical r →
        ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P),
          IsRationalLeviSubgroup l →
          ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (aL : A.toGrp ⟶ L),
            IsSplitComponent aL →
            ∃ a : A.toGrp ⟶ R, a ≫ r = aL ≫ l ∧ IsMaximalSplitTorus a

/-- Renard V.3.1: the unipotent radical `u : U ⟶ P` of a rational parabolic acts transitively
by conjugation on the split components of `P`. For two maximal split tori `a`, `a'` of the
radical `r : R ⟶ P` there are a rational point `q` of `U` and an isomorphism `e : A ≅ A'` with
`Int(q) ∘ (r ∘ a) = (r ∘ a') ∘ e`. -/
def ParabolicSplitComponentConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
        IsGeometricSolvableRadical r →
        ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ P),
          LeviSubgroup.IsGeometricUnipotentRadical u →
          ∀ (A A' : CommGroupScheme (Spec (CommRingCat.of k)))
            (a : A.toGrp ⟶ R) (a' : A'.toGrp ⟶ R),
            IsMaximalSplitTorus a → IsMaximalSplitTorus a' →
            ∃ q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
              ∃ e : A.toGrp ≅ A'.toGrp,
                a ≫ r ≫ (P.innerIso (q ≫ u.hom.hom)).hom = e.hom ≫ a' ≫ r

/-- Renard V.3.1: "Les sous-groupes de Levi `M` de `G` sont les centralisateurs de tores
déployés `A` dans `G` tels que `A` est la composante déployée de `M`." A homomorphism
`m : M ⟶ G` is a rational Levi factor of some rational parabolic of `G` if and only if it
represents the centralizer of a split subtorus `a : A ⟶ G` which, factored through `M`, is the
split component of `M`. -/
def LeviCentralizerCharacterizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (m : M ⟶ G),
      (∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
          IsParabolicSubgroup p ∧ IsRationalLeviSubgroup l ∧ l ≫ p = m) ↔
        ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
          (aM : A.toGrp ⟶ M),
          IsSplitSubtorus a ∧ (torusCentralizer a).IsRepresentedBy m ∧ aM ≫ m = a ∧
            IsSplitComponent aM

/-- Renard V.3.2: a rational parabolic `j : P ⟶ G` of a connected reductive group is minimal
if and only if its split component `a : A ⟶ R` (a maximal split torus of the radical
`r : R ⟶ P`) is a maximal split torus of `G`. -/
def MinimalParabolicSplitComponentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
        IsGeometricSolvableRadical r →
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ R),
          IsMaximalSplitTorus a →
          (IsMinimalParabolicSubgroup j ↔ IsMaximalSplitTorus (a ≫ r ≫ j))

/-- The five assertions of Renard V.3.1 and V.3.2 on split components of parabolic subgroups
stated in this module. -/
def ParabolicSplitComponentStatements : Prop :=
  ParabolicSplitComponentLeviStatement.{u} ∧ LeviSplitComponentRadicalStatement.{u} ∧
    ParabolicSplitComponentConjugacyStatement.{u} ∧
    LeviCentralizerCharacterizationStatement.{u} ∧ MinimalParabolicSplitComponentStatement.{u}

end Langlands.GroupScheme
