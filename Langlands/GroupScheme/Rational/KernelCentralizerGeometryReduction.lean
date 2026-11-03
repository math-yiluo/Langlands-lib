import Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement
import Langlands.GroupScheme.Torus.CocycleModelActionRelationSmoothStatement
import Langlands.GroupScheme.SmoothActionAffineOrbitStatement
import Langlands.GroupScheme.Rational.KernelCentralizerAffineQuotient
import Langlands.GroupScheme.Reductive.AffineHomogeneousQuotientStatement
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveStatement

/-! # Full-kernel centralizer quotients from three geometric inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeRoot

variable
  (hmodel : AutomorphicAction.AffineFiniteTypeCocycleModelStatement.{u})
  (hsmooth : Diagonalizable.CocycleModelActionRelationSmoothStatement.{u})
  (horbit : SchemeAction.SmoothActionAffineOrbitStatement.{u})

include hmodel hsmooth horbit

/-- The three geometric inputs give an actual affine homogeneous quotient of
any representative of the full kernel centralizer in a smooth affine group. -/
theorem exists_kernelCentralizerAffineQuotient_of_geometry
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (a : characterLattice S)
    {C : GroupScheme (Spec (CommRingCat.of k))}
    (j : C ⟶ G) (hrep : (kernelCentralizer i a).IsRepresentedBy j) :
    ∃ Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient j,
      IsAffineHom Q.scheme.hom := by
  let : AddGroup.FG (Diagonalizable.quotientLattice a) :=
    Diagonalizable.quotientLattice_fg S hS a
  let b := kernelDiagonalizableAction hS i a
  obtain ⟨M, hMaff, hMft⟩ := hmodel k
    (Diagonalizable.groupScheme (CommRingCat.of k)
      (Diagonalizable.quotientLattice a)).toGrp G b
  let : IsAffineHom M.scheme.hom := hMaff
  let : LocallyOfFiniteType M.scheme.hom := hMft
  have hrel : Smooth M.actionRelation.left :=
    hsmooth k (Diagonalizable.quotientLattice a) G b M
  obtain ⟨O, p, e, hOaff, _hOft, _hOqc, heopen, _heclosed,
    hp, hs, _hpqc, he⟩ :=
    horbit k G M.scheme M.action hrel M.basepoint
  let : IsAffineHom O.hom := hOaff
  let : IsOpenImmersion e.left := heopen
  let : Mono e := Over.mono_of_mono_left e
  have he' : p ≫ e = M.orbit := he
  exact ⟨kernelCentralizerAffineHomogeneousQuotient hS i a M j hrep
      O p e he' hp hs,
    kernelCentralizerAffineHomogeneousQuotient_isAffineHom hS i a M j hrep
      O p e he' hp hs⟩

/-- Choose the actual quotient supplied by the three geometric inputs. -/
def kernelCentralizerAffineQuotientOfGeometry
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (a : characterLattice S)
    {C : GroupScheme (Spec (CommRingCat.of k))}
    (j : C ⟶ G) (hrep : (kernelCentralizer i a).IsRepresentedBy j) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient j :=
  Classical.choose
    (exists_kernelCentralizerAffineQuotient_of_geometry hmodel hsmooth horbit
      S hS i a j hrep)

/-- Affineness is proved for the same chosen actual quotient. -/
theorem kernelCentralizerAffineQuotientOfGeometry_isAffineHom
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (a : characterLattice S)
    {C : GroupScheme (Spec (CommRingCat.of k))}
    (j : C ⟶ G) (hrep : (kernelCentralizer i a).IsRepresentedBy j) :
    IsAffineHom (kernelCentralizerAffineQuotientOfGeometry hmodel hsmooth horbit
      S hS i a j hrep).scheme.hom :=
  Classical.choose_spec
    (exists_kernelCentralizerAffineQuotient_of_geometry hmodel hsmooth horbit
      S hS i a j hrep)

/-- The exact target follows conditionally from the three geometric inputs and
the generic affine homogeneous quotient reductivity criterion. -/
theorem kernelCentralizerComponentReductive_of_geometry
    (hred : AffineHomogeneousQuotientReductiveStatement.{u}) :
    KernelCentralizerComponentReductiveStatement.{u} := by
  intro k _ G hG S hS i a _ha C j hrep hclosed hC
  let : Smooth C.X.hom := hC
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hclosed
  let : IsAffineHom C.X.hom := by
    have h : IsAffineHom (j.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  let : Smooth G.X.hom := hG.smooth
  exact hred k G hG C j hclosed hC
    (kernelCentralizerAffineQuotientOfGeometry hmodel hsmooth horbit
      S hS i a j hrep)
    (kernelCentralizerAffineQuotientOfGeometry_isAffineHom hmodel hsmooth horbit
      S hS i a j hrep)

end Langlands.GroupScheme.RelativeRoot
