import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle
import Langlands.AlgebraicGeometry.Picard.DualSchemeMap
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas

/-! # Canonical and cubic bundle transport under polarized isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Pullback of a diagonal Poincaré bundle along an abelian homomorphism is
the diagonal bundle for its contravariantly transported parameter map. -/
def poincareDiagonalHomPullbackIso (f : A ⟶ B)
    (hA : HasDualScheme A) (hB : HasDualScheme B)
    (lam : B.X ⟶ dualScheme B hB) :
    (LineBundle.pullback (hom f)).obj (poincareDiagonalBundle B hB lam) ≅
      poincareDiagonalBundle A hA
        ((groupHom f).hom.hom ≫ lam ≫ dualSchemeMap homPicardZeroPullback f hA hB) := by
  let PA := (RigidifiedLineBundle.forget _).obj (poincareFamily A hA)
  let PB := (RigidifiedLineBundle.forget _).obj (poincareFamily B hB)
  let q := relativeDiagonal A ≫
    (relativeSpace A.X.hom).map ((groupHom f).hom.hom ≫ lam)
  let e := (RigidifiedLineBundle.forget _).mapIso
    (dualSchemeMapPullbackIso homPicardZeroPullback f hA hB)
  change (LineBundle.pullback ((relativeSpace A.X.hom).map
      (dualSchemeMap homPicardZeroPullback f hA hB))).obj PA ≅
    (LineBundle.pullback ((homFamilySpaceMap f).app (dualScheme B hB))).obj PB at e
  have hq : q ≫ (homFamilySpaceMap f).app (dualScheme B hB) =
      hom f ≫ relativeDiagonal B ≫ (relativeSpace B.X.hom).map lam := by
    apply pullback.hom_ext
    · simp [q, relativeDiagonal, relativeSpace, Category.assoc, homFamilySpaceMap]
      change (𝟙 A.X.left) ≫ hom f ≫ lam.left =
        hom f ≫ (𝟙 B.X.left) ≫ lam.left
      simp only [Category.id_comp]
    · simp [q, relativeDiagonal, relativeSpace, Category.assoc, homFamilySpaceMap]
      change (𝟙 A.X.left) ≫ hom f = hom f
      simp only [Category.id_comp]
  have hq' : q ≫ (relativeSpace A.X.hom).map
      (dualSchemeMap homPicardZeroPullback f hA hB) =
      relativeDiagonal A ≫ (relativeSpace A.X.hom).map
        ((groupHom f).hom.hom ≫ lam ≫ dualSchemeMap homPicardZeroPullback f hA hB) := by
    simp only [q, Functor.map_comp, Category.assoc]
  change (LineBundle.pullback (hom f)).obj
      ((LineBundle.pullback (relativeDiagonal B)).obj
        ((LineBundle.pullback ((relativeSpace B.X.hom).map lam)).obj PB)) ≅ _
  exact (LineBundle.pullbackComp (hom f) (relativeDiagonal B)).app _ ≪≫
    (LineBundle.pullbackComp _ ((relativeSpace B.X.hom).map lam)).app PB ≪≫
    (LineBundle.pullbackEqIso hq PB).symm ≪≫
    ((LineBundle.pullbackComp q _).app PB).symm ≪≫
    (LineBundle.pullback q).mapIso e.symm ≪≫
    LineBundle.pullbackCompEqIso q _ hq' PA ≪≫
    ((LineBundle.pullbackComp (relativeDiagonal A) _).app PA).symm

namespace PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {g d n : ℕ}
  {a b : Datum P S g d n}

/-- The polarization equation is the exact equation of parameter-scheme maps. -/
lemma PolarizedIso.parameterMap_eq (α : PolarizedIso a b) :
    a.dualWitness.parameterMap P a.polarization =
      (groupHom α.abelianIso.hom).hom.hom ≫
        b.dualWitness.parameterMap P b.polarization ≫
          dualSchemeMap homPicardZeroPullback α.abelianIso.hom
            a.dualWitness.hasDual b.dualWitness.hasDual :=
  congrArg (fun k ↦ (groupHom k).hom.hom) α.polarization_eq

/-- A polarized isomorphism transports the actual canonical diagonal bundle. -/
def PolarizedIso.canonicalBundlePullbackIso (α : PolarizedIso a b) :
    (LineBundle.pullback (hom α.abelianIso.hom)).obj b.canonicalBundle ≅
      a.canonicalBundle :=
  poincareDiagonalHomPullbackIso α.abelianIso.hom
      a.dualWitness.hasDual b.dualWitness.hasDual
      (b.dualWitness.parameterMap P b.polarization) ≪≫
    eqToIso (congrArg (poincareDiagonalBundle a.abelian a.dualWitness.hasDual)
      α.parameterMap_eq.symm)

/-- Tensor-cubing the canonical comparison gives the actual cubic-bundle
pullback isomorphism, with no preservation witness supplied by the caller. -/
def PolarizedIso.cubicBundlePullbackIso (α : PolarizedIso a b) :
    (Scheme.Modules.pullback (hom α.abelianIso.hom)).obj b.cubicBundle.obj ≅
      a.cubicBundle.obj :=
  actualPullbackTensorPowIso _ b.canonicalBundle.obj 3 ≪≫
    tensorPowIso ((LineBundle.forget _).mapIso α.canonicalBundlePullbackIso) 3

end PolarizedFiniteLevel

end Langlands.AbelianScheme
