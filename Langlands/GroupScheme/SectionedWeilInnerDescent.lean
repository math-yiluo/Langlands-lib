import Langlands.GroupScheme.SectionedQuotientExtension
import Langlands.GroupScheme.VectorBundleWeilCocycle
import Langlands.GroupScheme.RelativeInnerCocycle
import Langlands.GroupScheme.FppfLocalGroupIso

/-! # Inner-isomorphism descent through sectioned Weil quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {S : Scheme.{u}} {G A P : GroupScheme S}

/-- Faithfulness on all tests is preserved on a monic subgroup. -/
theorem IsFaithful.restrict_mono {c : AutomorphicAction A G} (hc : c.IsFaithful)
    (j : P ⟶ A) [Mono j.hom.hom] : (c.restrict j).IsFaithful := by
  intro V x y hxy
  apply (cancel_mono j.hom.hom).mp
  apply hc
  intro W t g
  simpa only [Category.assoc, restrict_act] using hxy t g

end AutomorphicAction

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {V : Over S}
    [Flat V.hom] [Surjective V.hom] [LocallyOfFinitePresentation V.hom]

/-- The descended isomorphism has the prescribed local value wherever a
point of the original cover is supplied. -/
theorem comp_descendFppf_eq (e : LocalGroupIso G H V) (he : e.IsIndependent)
    {W : Over S} (b : W ⟶ V) (g : W ⟶ G.X) :
    g ≫ (e.descendFppf he).hom.hom.hom = e.toFun b g := by
  change g ≫ (e.toLocalGroupHom.descendFppf he).hom.hom =
    e.toLocalGroupHom.toFun b g
  exact (e.toLocalGroupHom.comp_descendFppf he W g).trans (by
    simpa only [Category.id_comp] using
      e.toLocalGroupHom.comp_valueFppf he (𝟙 W) b g)

end LocalGroupIso

namespace SectionedQuotientExtension

variable {A C : CommRingCat.{u}} [Algebra A C]
    [Module.Finite A C] [Module.Projective A C]
    {K B T Z P D : GroupScheme (Spec A)}
    (i : K ⟶ B) (p : B ⟶ T) (t : T ⟶ B) (z : Z ⟶ T)
    (qB : B ⟶ P) (qT : T ⟶ D)
    (ht : t ≫ p = 𝟙 T)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hB : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (z ≫ t)) qB)
    (hT : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) qT)
    [Mono i.hom.hom] [IsAffine P.X.left] [IsAffineHom K.X.hom]
    (hK : RelativeUnipotent.HasFiniteVectorBundleSeries K)
    (eD : D ≅ WeilGm.groupScheme A C)
    {V : Over (Spec A)} [Flat V.hom] [Surjective V.hom]
    [LocallyOfFinitePresentation V.hom]

include ht hp hB hT hK eD

/-- Vanishing for the constructed quotient uses the original kernel and its
supplied vector-bundle series. The new quotient map is not an extra premise. -/
theorem cocycle_isTrivial_of_pic_trivial [Subsingleton (CommRing.Pic C)]
    (ξ : Cocycle P V) : ξ.IsTrivial := by
  let r := hom p t z qB qT ht hB hT
  let : Mono (i ≫ qB).hom.hom := inclusion_mono i p t z qB ht hp hB
  let : IsIso eD.hom.hom.hom.left :=
    (Over.forget (Spec A)).map_isIso eD.hom.hom.hom
  let : IsAffine (WeilGm.groupScheme A C).X.left := by
    change IsAffine (Spec _)
    infer_instance
  let : IsAffine D.X.left := IsAffine.of_isIso eD.hom.hom.hom.left
  have hr := isFppfQuotient i p t z qB qT ht hp hB hT
  let : Flat r.hom.hom.left := hr.1
  let : Surjective r.hom.hom.left := hr.2.1
  let : LocallyOfFinitePresentation r.hom.hom.left := hr.2.2.1
  exact ξ.isTrivial_of_vectorBundleSeries_weilExtension_fppf_of_pic_trivial
    (i ≫ qB) r hr.2.2.2 hK eD

/-- Choose a primitive on the original single fppf cover. -/
def picardCochain [Subsingleton (CommRing.Pic C)] (ξ : Cocycle P V) : V ⟶ P.X :=
  Classical.choose
    (cocycle_isTrivial_of_pic_trivial i p t z qB qT ht hp hB hT hK eD ξ)

/-- The chosen primitive gives the coboundary equation on every test scheme. -/
theorem picardCochain_spec [Subsingleton (CommRing.Pic C)] (ξ : Cocycle P V)
    {W : Over (Spec A)} (a b : W ⟶ V) :
    ξ.toFun a b =
      (a ≫ picardCochain i p t z qB qT ht hp hB hT hK eD ξ) *
      (b ≫ picardCochain i p t z qB qT ht hp hB hT hK eD ξ)⁻¹ :=
  Classical.choose_spec
    (cocycle_isTrivial_of_pic_trivial i p t z qB qT ht hp hB hT hK eD ξ) a b

/-- The Picard hypothesis follows from finite-algebra Picard triviality. -/
theorem cocycle_isTrivial_of_finiteAlgebrasHaveTrivialPicard
    (hA : Langlands.Algebra.FiniteAlgebrasHaveTrivialPicard.{u, u} A)
    (ξ : Cocycle P V) : ξ.IsTrivial := by
  let : Subsingleton (CommRing.Pic C) := hA C
  exact cocycle_isTrivial_of_pic_trivial i p t z qB qT ht hp hB hT hK eD ξ

/-- Semi-locality gives vanishing for the constructed quotient. -/
theorem cocycle_isTrivial_of_semilocal [Finite (MaximalSpectrum A)]
    (ξ : Cocycle P V) : ξ.IsTrivial :=
  cocycle_isTrivial_of_finiteAlgebrasHaveTrivialPicard
    i p t z qB qT ht hp hB hT hK eD
    (Langlands.Algebra.finiteAlgebrasHaveTrivialPicard_of_semilocal A) ξ

variable {G H : GroupScheme (Spec A)}
    (e : LocalGroupIso G H V) (c : AutomorphicAction P G)
    (hc : c.IsFaithful) (he : e.HasInnerDiscrepancy c)

/-- Pointwise inner discrepancies in the sectioned quotient produce an actual
global isomorphism, with no supplied cocycle or naturality data. -/
def innerIsoOfPicTrivial [Subsingleton (CommRing.Pic C)] : G ≅ H :=
  let ξ := e.innerCocycle c hc he
  let f := picardCochain i p t z qB qT ht hp hB hT hK eD ξ
  (e.twist c f).descendFppf
    (e.twist_isIndependent c ξ (e.innerCocycle_hasDiscrepancy c hc he) f
      (picardCochain_spec i p t z qB qT ht hp hB hT hK eD ξ))

/-- On the original cover, the global isomorphism is the local map corrected
by the selected sectioned-quotient primitive. -/
theorem innerIsoOfPicTrivial_spec [Subsingleton (CommRing.Pic C)]
    {W : Over (Spec A)} (b : W ⟶ V) (g : W ⟶ G.X) :
    g ≫ (innerIsoOfPicTrivial i p t z qB qT ht hp hB hT hK eD e c hc he).hom.hom.hom =
      e.toFun b
        (c.act (b ≫ picardCochain i p t z qB qT ht hp hB hT hK eD
          (e.innerCocycle c hc he)) g) := by
  let ξ := e.innerCocycle c hc he
  let f := picardCochain i p t z qB qT ht hp hB hT hK eD ξ
  have hind : (e.twist c f).IsIndependent :=
    e.twist_isIndependent c ξ (e.innerCocycle_hasDiscrepancy c hc he) f
      (picardCochain_spec i p t z qB qT ht hp hB hT hK eD ξ)
  exact LocalGroupIso.comp_descendFppf_eq (e.twist c f) hind b g

/-- The same actual isomorphism construction over a semi-local ring. -/
def innerIsoOfSemilocal [Finite (MaximalSpectrum A)] : G ≅ H := by
  let : Subsingleton (CommRing.Pic C) :=
    Langlands.Algebra.finiteAlgebrasHaveTrivialPicard_of_semilocal A C
  exact innerIsoOfPicTrivial i p t z qB qT ht hp hB hT hK eD e c hc he

variable {Gad : GroupScheme (Spec A)} (q : G ⟶ Gad)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction Gad G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G))
    (j : P ⟶ Gad) [Mono j.hom.hom]

/-- A central-quotient action is automatically faithful on the supplied
monic sectioned quotient, so only pointwise discrepancy representation is needed. -/
def centralQuotientInnerIsoOfSemilocal [Finite (MaximalSpectrum A)]
    (hj : e.HasInnerDiscrepancy (a.restrict j)) : G ≅ H :=
  innerIsoOfSemilocal i p t z qB qT ht hp hB hT hK eD e (a.restrict j)
    (AutomorphicAction.IsFaithful.restrict_mono
      (a.centralQuotient_action_isFaithful q hq ha) j) hj

end SectionedQuotientExtension

end Langlands.GroupScheme
