import Langlands.GroupScheme.RelativeLevi.SplitFaceEtaleComparison
import Langlands.GroupScheme.RelativeUnipotent.LinearQuotientComparison

/-! # Actual supplied-radical and quotient comparisons of canonical face series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open RelativeUnipotent LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  [DecidableEq I] [DecidableEq I']
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {fam : J → (Ga R ⟶ G)} {fam' : J' → (Ga R ⟶ G)}
  {wt : I → ℤ} {wt' : I' → ℤ}
  (C : SplitParabolicFaceChart i P fam wt) (D : SplitParabolicFaceChart j Q fam' wt')

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

section SuppliedRadical

variable {H U : GroupScheme (Spec (CommRingCat.of R))} {p : H ⟶ G} (r : U ⟶ H)
  (hG : IsReductive G)
  (hPar : (Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).IsRepresentedBy p)
  (hr : IsRelativeUnipotentRadical r)

/-- The actual initial face term is the supplied radical, preserving its
original ambient map and without a nontrivial-ring premise. -/
def suppliedRadicalIso : C.weights.groupScheme 0 ≅ U :=
  C.represented.isoOfIsRepresentedBy
    (RelativeLevi.isRepresentedBy_unipotent_of_relativeRadical
      dynamicRelativeLevi hG (AffineRegularBorel.cocharacter i wt) hPar r hr)

/-- The supplied radical is retained with its prescribed inclusion. -/
theorem suppliedRadicalIso_hom_comp :
    (C.suppliedRadicalIso r hG hPar hr).hom ≫ (r ≫ p) =
      C.weights.inclusion 0 ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end SuppliedRadical

variable [Nontrivial R]
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' G j Q)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization j (Q.root a) (fam' a))
  (hU : Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) =
    Dynamic.unipotent (AffineRegularBorel.cocharacter j wt'))
  (hPar : Dynamic.parabolic (AffineRegularBorel.cocharacter i wt) =
    Dynamic.parabolic (AffineRegularBorel.cocharacter j wt'))

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- The original-inclusion-compatible term comparisons intertwine the actual
successive inclusions of the two canonical face series. -/
theorem step_comp_sameParabolicTermIso (d : ℕ) :
    C.weights.step d ≫
      (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom =
    (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar (d + 1)).hom ≫
      D.weights.step d := by
  let b := D.weights.inclusion d ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)
  have hm : Mono b.hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)).1
  have hb : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨hm, rfl⟩
  apply hb.hom_ext
  change (C.weights.step d ≫ _ ) ≫ (D.weights.inclusion d ≫ _) =
    (_ ≫ D.weights.step d) ≫ (D.weights.inclusion d ≫ _)
  rw [Category.assoc, C.sameParabolicTermIso_hom_comp D hG hmax hmax' hP hQ hfam hfam'
    hU hPar d]
  rw [← Category.assoc, C.weights.step_comp_inclusion,
    Category.assoc, ← Category.assoc (D.weights.step d), D.weights.step_comp_inclusion,
    C.sameParabolicTermIso_hom_comp D hG hmax hmax' hP hQ hfam hfam' hU hPar (d + 1)]

/-- Canonical comparison of the actual full fppf vector quotients induced by
the two compatible consecutive-term comparisons. -/
def sameParabolicQuotientIso (d : ℕ) :
    VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (C.weights.exactSupport d)) ≅
      VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (D.weights.exactSupport d)) :=
  FppfQuotientComparison.isoOfCompatibleTerms (C.weights.step d) (D.weights.step d)
    (C.weights.isFppfQuotient_quotientMap d) (D.weights.isFppfQuotient_quotientMap d)
    (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d)
    (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar (d + 1))
    (C.step_comp_sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d)

/-- The actual quotient comparison commutes with the original quotient maps. -/
theorem quotientMap_comp_sameParabolicQuotientIso (d : ℕ) :
    C.weights.quotientMap d ≫
      (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom =
    (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom ≫
      D.weights.quotientMap d :=
  FppfQuotientComparison.isoOfCompatibleTerms_fac _ _ _ _ _ _ _

section TwoPresentations

variable {H U : GroupScheme (Spec (CommRingCat.of R))} {p : H ⟶ G} (r : U ⟶ H)
  (hParC : (Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).IsRepresentedBy p)
  (hParD : (Dynamic.parabolic (AffineRegularBorel.cocharacter j wt')).IsRepresentedBy p)
  (hr : IsRelativeUnipotentRadical r)

/-- For two presentations of the same supplied radical, the actual term
comparison needs no separate equality assumptions on the dynamic functors. -/
def sameSuppliedRadicalTermIso (d : ℕ) : C.weights.groupScheme d ≅ D.weights.groupScheme d :=
  C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam'
    (RelativeLevi.unipotent_eq_of_same_suppliedRadical
      (AffineRegularBorel.cocharacter i wt) (AffineRegularBorel.cocharacter j wt') r
      hG hParC hParD hr)
    (hParC.2.symm.trans hParD.2) d

/-- Its equation retains exactly the original ambient maps. -/
theorem sameSuppliedRadicalTermIso_hom_comp (d : ℕ) :
    (C.sameSuppliedRadicalTermIso D hG hmax hmax' hP hQ hfam hfam' r hParC hParD hr d).hom ≫
      (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)) =
      C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter) :=
  C.sameParabolicTermIso_hom_comp D hG hmax hmax' hP hQ hfam hfam' _ _ d

end TwoPresentations

end Langlands.GroupScheme.SplitParabolicFaceChart
