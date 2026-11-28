import Langlands.Representation.CuspidalSupport.BernsteinParabolicStandardization
import Langlands.Representation.CuspidalSupport.BernsteinInnerInertia
import Langlands.Representation.CuspidalSupport.BernsteinComponentWeylGroup
import Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsReduction
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar

/-! # Twisted cuspidal induction through a represented parabolic -/

noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

open ComponentWeyl RepresentedParabolic

universe u v

attribute [local instance] ambientAffine canonicalTopology standardLeviClosed standardLeviAffine
  BernsteinLeviPresentation.standardLeviFiniteType

/-- A central endomorphism acts by a scalar on the specified representation. -/
def ActsByScalar
    {Q : Type u} [Group Q] [TopologicalSpace Q]
    (z : CatCenter (SmoothRep.{0, u, v} ℂ Q))
    (V : SmoothRep.{0, u, v} ℂ Q) (c : ℂ) : Prop :=
  ∀ x : V, SmoothRep.hom (z.app V) x = c • x

private theorem centerScalar_of_iso
    {Q : Type u} [Group Q] [TopologicalSpace Q]
    (z : CatCenter (SmoothRep.{0, u, v} ℂ Q))
    {V W : SmoothRep.{0, u, v} ℂ Q} (e : V ≅ W) {c : ℂ}
    (h : ActsByScalar z V c) : ActsByScalar z W c :=
  SmoothRep.centerScalar_of_surjective (𝟭 _) z e.hom
    (fun y => ⟨SmoothRep.hom e.inv y, congrArg (fun f => SmoothRep.hom f y) e.inv_hom_id⟩) h

private theorem ActsByScalar.unique
    {Q : Type u} [Group Q] [TopologicalSpace Q]
    (z : CatCenter (SmoothRep.{0, u, v} ℂ Q))
    (V : SmoothRep.{0, u, v} ℂ Q) (hnt : Nontrivial V) {c d : ℂ}
    (hc : ActsByScalar z V c) (hd : ActsByScalar z V d) : c = d :=
  letI := hnt
  SmoothRep.scalar_unique (z.app V) hc hd

section TwistInduction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {family : BernsteinStandardFamily i ν}

/-- Normalized induction of an unramified twist of the inducing representation. -/
abbrev BernsteinCuspidalDatum.twistInduction
    (a : BernsteinCuspidalDatum.{u, v} i ν family) (χ : UChar (bernsteinLeviScheme i ν a.roots)) :=
  (normalizedInductionFunctor (family.decomposition a.roots) (family.closedUnipotent a.roots)).obj
    (bernsteinLiteralLeviRep i ν a.roots (rationalUnramifiedTwist _ χ a.representation))

set_option backward.isDefEq.respectTransparency.types false in
private theorem centerScalar_compare_inner
    {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]
    {J : Finset (SimpleRoot i ν)} {j : M ⟶ G} (D : BernsteinLeviPresentation i ν J j)
    (a : BernsteinCuspidalDatum.{u, max u v} D.torus ν (D.standardFamily family))
    (χ : UChar (bernsteinLeviScheme D.torus ν a.roots))
    (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G))) {c d : ℂ} :
    let V := a.twistInduction χ
    let outer := normalizedInductionFunctor.{u, max u v} (family.decomposition J) (family.closedUnipotent J)
    let W := outer.obj (SmoothRep.pullback D.points.symm V)
    let b := (D.ambientDatum family a).val
    let ω : UChar (bernsteinLeviScheme i ν b.roots) :=
      rationalUnramifiedCharacterTransport (D.innerLeviIso family a.roots) χ
    let B := b.twistInduction ω
    ActsByScalar z W c → ActsByScalar z B d → c = d := by
  intro V outer W b ω B h hd
  let σ := rationalUnramifiedTwist _ χ a.representation
  let inner := D.innerInductionStagesIso.{u, v} family a.roots σ
  have hInner := centerScalar_of_iso z inner h
  let direct := normalizedInductionFunctor.{u, max u v} (family.decomposition b.roots)
    (family.closedUnipotent b.roots)
  let literal := SmoothRep.pullbackFunctor (leviRationalPointHomeomorph i ν b.roots).symm
  let twist := direct.mapIso (literal.mapIso
    (rationalIsoPullbackTwistIso (D.innerLeviIso family a.roots).symm χ a.representation))
  have hc : ActsByScalar z B c := centerScalar_of_iso z twist hInner
  have hnt : Nontrivial B := by
    with_reducible exact nontrivial_twistInduction i ν family b ω
  exact ActsByScalar.unique z B hnt hc hd

end TwistInduction

namespace BernsteinParabolicPresentation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G P M N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} (A : BernsteinParabolicPresentation p l r)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The actual Levi of the parabolic represents the displayed standard Levi. -/
theorem leviPresentation (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) :
    BernsteinLeviPresentation A.inclusion A.cocharacter A.roots (l ≫ p) := by
  have hc : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  refine ⟨hl.isConnectedReductive, hc, ?_⟩
  rw [← A.levi_eq]
  exact hc.isRepresentedBy_range

variable [IsAffineHom M.X.hom]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The two identifications of the represented Levi with the standard point group agree. -/
theorem leviPoints_eq : A.leviPoints hp hl = (A.leviPresentation hp hl).points := by
  refine ContinuousMulEquiv.ext fun m => Subtype.ext ?_
  exact (A.leviPoints_apply_coe hp hl m).trans
    ((A.leviPresentation hp hl).points_apply_coe m).symm

variable [T2Space F]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hmul : IsIso (subgroupMultiplication l r))

/-- Represented induction expressed using the point identification of the Levi presentation. -/
def inductionObjIsoOfLeviPresentation
    (V : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) :
    (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj V ≅
      (normalizedInductionFunctor.{u, max u v} (A.family.decomposition A.roots)
        (A.family.closedUnipotent A.roots)).obj
        (SmoothRep.pullback (A.leviPresentation hp hl).points.symm V) := by
  rw [← A.leviPoints_eq hp hl]
  exact A.inductionObjIso.{u, max u v} hp hl hr hmul V

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [LocallyOfFiniteType M.X.hom] [LocallyCompactSpace (rationalPoints M)]
  [NonarchimedeanGroup (rationalPoints M)] in
private theorem induction_centerScalar
    (V : SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
    (zM : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)))
    (hind : ∀ σ, (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).map (zM.app σ) =
      z.app ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ))
    {c : ℂ} (hc : ActsByScalar zM V c) :
    let W := (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj V
    ActsByScalar z W c := by
  intro W y
  let I := leviInductionFunctor.{u, max u v} p l r hp hr hl hmul
  have hzM : zM.app V = c • 𝟙 V := by
    apply ObjectProperty.hom_ext
    ext x
    exact hc x
  change SmoothRep.hom (z.app (I.obj V)) y = c • y
  rw [← hind, hzM]
  rfl

/-- Central scalars on corresponding twisted inductions agree for a homomorphism
compatible with the represented induction functor. -/
def TwistInductionScalarsAgree : Prop :=
  let D := A.leviPresentation hp hl
  ∀ (a : BernsteinCuspidalDatum.{u, max u v} D.torus A.cocharacter (D.standardFamily A.family))
  (χ : UChar (bernsteinLeviScheme D.torus A.cocharacter a.roots))
  (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
  (zM : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)))
  {c d : ℂ},
    (∀ σ, (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).map (zM.app σ) =
      z.app ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ)) →
    ActsByScalar zM (a.twistInduction χ) c →
    (let b := (D.ambientDatum A.family a).val
     let ω : UChar (bernsteinLeviScheme A.inclusion A.cocharacter b.roots) :=
       rationalUnramifiedCharacterTransport (D.innerLeviIso A.family a.roots) χ
     ActsByScalar z (b.twistInduction ω) d) → c = d

/-- The central scalar is preserved by represented induction and by the comparison with
standard induction from the transported cuspidal datum. -/
theorem twistInduction_scalar_eq : A.TwistInductionScalarsAgree.{u, v} hp hl hr hmul := by
  unfold TwistInductionScalarsAgree
  intro D a χ z zM c d hind hc hd
  have h := induction_centerScalar.{u, v} hp hl hr hmul (a.twistInduction χ) z zM hind hc
  let e := A.inductionObjIsoOfLeviPresentation.{u, v} hp hl hr hmul (a.twistInduction χ)
  let W := (normalizedInductionFunctor.{u, max u v} (A.family.decomposition A.roots)
    (A.family.closedUnipotent A.roots)).obj (SmoothRep.pullback D.points.symm (a.twistInduction χ))
  have hOuter : ActsByScalar z W c := centerScalar_of_iso z e h
  have hCompare := centerScalar_compare_inner.{u, v}
    (i := A.inclusion) (ν := A.cocharacter) (family := A.family)
    (J := A.roots) (j := l ≫ p) D a χ z (c := c) (d := d)
  dsimp only at hCompare hd
  with_reducible exact hCompare hOuter hd

end BernsteinParabolicPresentation

end Langlands.CuspidalSupport
