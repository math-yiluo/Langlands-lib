/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.Line.LineQuotientHomogeneousFractionMap

/-!
# Inverse line-quotient charts and arbitrary pullback

The classifying morphism is specified by the existing homogeneous-fraction charts.
Quantification over every such morphism avoids making a second choice of that map.

## References

* Stacks Project, Constructions
* Stacks, Constructions, Tag 01OA
* Stacks, Constructions, Tags 01OA and 01O4
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry

open Scheme.Modules

local instance instModuleRestrictedSections (T : Scheme.{u}) (L : T.Modules)
    {U V : T.Opens} (h : V ≤ U) :
    Module Γ(T, V)
      ((ModuleCat.restrictScalars (T.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (L.val.obj (op V))) :=
  inferInstanceAs (Module Γ(T, V) (L.val.obj (op V)))

/-- Pull back the quotient using the section-normalized composite-pullback comparison. -/
noncomputable def lineQuotientPullback {S T T' : Scheme.{u}} (h : T ⟶ S)
    (u : T' ⟶ T) (E : S.Modules) (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L) :
    (tensorPullback (u ≫ h)).obj E ⟶ (tensorPullback u).obj L :=
  (tensorPullbackSectionComp u h).hom.app E ≫ (tensorPullback u).map q

/-- The normalized tautological section associated with a degree-one generator.
The datum's chart equation identifies this section with iota(m)/1 in the twist. -/
noncomputable def tautologicalGenerator {S : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (U : S.affineOpens)
    (m : Γ(E, U.1)) :
    Γ(D.line, (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1) :=
  ((tensorPullbackSectionAdjunction
    (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).homEquiv E D.line
      D.quotient).app U.1 m

/-- The actual pullback of the normalized degree-one tautological section, restricted
onto an arbitrary open. This is the pulled frame e on a generator chart. -/
noncomputable def pulledTautologicalGenerator {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (U : S.affineOpens) (V : T.Opens)
    (hVF : V ≤ F ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (m : Γ(E, U.1)) : Γ((tensorPullback F).obj D.line, V) :=
  ((tensorPullback F).obj D.line).val.map (homOfLE hVF).op
    (tensorPullbackSection F D.line
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
      (tautologicalGenerator D U m))

/-- Sectionwise chart normalization of the inverse line isomorphism. In particular, on
D(b_m) the pulled frame e goes to b_m*l. Taking any v in place of m gives b_v*l;
the fraction-chart equation identifies its pulled quotient coefficient with b_v/b_m.
The equation on every smaller open expresses compatibility on all overlaps and refinements. -/
def InverseLineChartNormalization {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (θ : (tensorPullback F).obj D.line ≅ L) : Prop :=
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)), IsFreeGenerator l →
    ∀ (m : Γ(E, U.1)) (V : T.Opens) (hVW : V ≤ W.1)
      (hVF : V ≤ F ⁻¹ᵁ
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)),
      θ.hom.app V (pulledTautologicalGenerator D F U V hVF m) =
        T.presheaf.map (homOfLE hVW).op
          (quotientGeneratorCoefficient h E L q U W hWU l m) •
            L.val.map (homOfLE hVW).op l ∧
      (IsUnit (T.presheaf.map (homOfLE hVW).op
          (quotientGeneratorCoefficient h E L q U W hWU l m)) →
        IsFreeGenerator (pulledTautologicalGenerator D F U V hVF m) ∧
        ∀ v : Γ(E, U.1),
          θ.hom.app V (pulledTautologicalGenerator D F U V hVF v) =
            (T.presheaf.map (homOfLE hVW).op
                (quotientGeneratorCoefficient h E L q U W hWU l v) *
              Ring.inverse (T.presheaf.map (homOfLE hVW).op
                (quotientGeneratorCoefficient h E L q U W hWU l m))) •
            (T.presheaf.map (homOfLE hVW).op
                (quotientGeneratorCoefficient h E L q U W hWU l m) •
              L.val.map (homOfLE hVW).op l)) ∧
      ∀ n : Γ(E, U.1),
        IsUnit (T.presheaf.map (homOfLE hVW).op
          (quotientGeneratorCoefficient h E L q U W hWU l n)) →
        pulledTautologicalGenerator D F U V hVF m =
          (T.presheaf.map (homOfLE hVW).op
              (quotientGeneratorCoefficient h E L q U W hWU l m) *
            Ring.inverse (T.presheaf.map (homOfLE hVW).op
              (quotientGeneratorCoefficient h E L q U W hWU l n))) •
            pulledTautologicalGenerator D F U V hVF n

/-- On a chart pulled back along a, use the pulled tautological generator itself as frame.
Its own quotient coefficient is one. The all-degree fraction charts then recover the ring
map of a on every c/e^d, including degree zero. -/
def RecoveredQuotientFrame {S T : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    (D : TautologicalQuotient E) (h : T ⟶ S)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h) : Prop :=
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (hWa : W.1 ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (m : Γ(E, U.1)) (l : Γ((tensorPullback a).obj D.line, W.1)),
    l = ((tensorPullback a).obj D.line).val.map (homOfLE hWa).op
      (tensorPullbackSection a D.line
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
        (tautologicalGenerator D U m)) →
    IsFreeGenerator l →
    quotientGeneratorCoefficient h E ((tensorPullback a).obj D.line)
      (pulledQuotient D h a ha) U W hWU l m = 1

/-- The recovered all-degree chart ring map is exactly pullback by a: the coefficient
of c in the pulled e frame is a^*(c/e^d). The map k is the factorization of a into
Spec (A_e)_0, so appTop and the canonical affine section isomorphisms give its ring map. -/
def RecoveredFractionCoefficients {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E)
      ((tensorPullback a).obj D.line)) : Prop :=
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (hWa : W.1 ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (m : Γ(E, U.1))
    (k : W.1.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val))),
    W.1.ι ≫ a = k ≫
      Proj.awayι ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val (quotientSymmetricGenerator E U m).property
        (by decide : 0 < (1 : ℕ)) ≫
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U →
    ∀ (d : ℕ) (c : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
      ψ.quotientCoefficient U W hWU
        (pulledTautologicalGenerator D a U W.1 hWa m) d c =
      W.1.topIso.hom (k.appTop ((Scheme.ΓSpecIso _).inv
        (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
          (quotientSymmetricGenerator E U m) d c)))

/-- Arbitrary pullback sends all homogeneous coefficients and all degree-zero fractions
to the fractions of their images. The localization homomorphism is fixed on every scalar,
so it is the canonical localization map rather than an arbitrary comparison. -/
def QuotientFractionNaturality {S T T' : Scheme.{u}} (h : T ⟶ S) (u : T' ⟶ T)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (ψ' : RelativeGradedLineMap (u ≫ h) (SymmetricAlgebraSheaf.gradedAlgebraData E)
      ((tensorPullback u).obj L)) : Prop :=
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)), IsFreeGenerator l →
    ∀ (W' : T'.affineOpens) (hWW' : W'.1 ≤ u ⁻¹ᵁ W.1)
      (hW'U : W'.1 ≤ (u ≫ h) ⁻¹ᵁ U.1),
      (∀ (d : ℕ) (z : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
        ψ'.quotientCoefficient U W' hW'U
          (((tensorPullback u).obj L).val.map (homOfLE hWW').op
            (tensorPullbackSection u L W.1 l)) d z =
          u.appLE W.1 W'.1 hWW' (ψ.quotientCoefficient U W hWU l d z)) ∧
      ∀ m : Γ(E, U.1),
        quotientGeneratorCoefficient (u ≫ h) E ((tensorPullback u).obj L)
          (lineQuotientPullback h u E L q) U W' hW'U
          (((tensorPullback u).obj L).val.map (homOfLE hWW').op
            (tensorPullbackSection u L W.1 l)) m =
          u.appLE W.1 W'.1 hWW' (quotientGeneratorCoefficient h E L q U W hWU l m) ∧
        ∃ β : Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m) →+*
            Localization.Away (u.appLE W.1 W'.1 hWW'
              (quotientGeneratorCoefficient h E L q U W hWU l m)),
          (∀ b : Γ(T, W.1),
            β (algebraMap Γ(T, W.1) _ b) =
              algebraMap Γ(T', W'.1) _ (u.appLE W.1 W'.1 hWW' b)) ∧
          ∀ (d : ℕ) (z : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
            β (Localization.mk (ψ.quotientCoefficient U W hWU l d z)
              (⟨quotientGeneratorCoefficient h E L q U W hWU l m ^ d,
                ⟨d, rfl⟩⟩ : Submonoid.powers
                  (quotientGeneratorCoefficient h E L q U W hWU l m))) =
              Localization.mk
                (u.appLE W.1 W'.1 hWW' (ψ.quotientCoefficient U W hWU l d z))
                (⟨u.appLE W.1 W'.1 hWW'
                    (quotientGeneratorCoefficient h E L q U W hWU l m) ^ d,
                  ⟨d, rfl⟩⟩ : Submonoid.powers (u.appLE W.1 W'.1 hWW'
                    (quotientGeneratorCoefficient h E L q U W hWU l m)))

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
