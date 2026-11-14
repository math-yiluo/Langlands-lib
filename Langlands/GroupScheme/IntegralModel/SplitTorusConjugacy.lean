import Langlands.GroupScheme.Torus.HenselianSplitTorusConjugacy
import Langlands.GroupScheme.IntegralModel.HenselianTransporter
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Split-torus conjugacy through a supplied integral model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  {T T' : CommGroupScheme (Spec (CommRingCat.of R))}
  {i : T.toGrp ⟶ M.group} {i' : T'.toGrp ⟶ M.group}

namespace SplitTorusConjugator

variable (A : SplitTorusConjugator i i')

/-- The same integral conjugator read through the model's specified generic
identification. -/
def genericPoint : rationalPoints G :=
  M.integralPointMap A.section_

theorem genericPoint_mem_integralPoints :
    A.genericPoint M ∈ M.integralPoints :=
  ⟨A.section_, rfl⟩

/-- The integral conjugacy equation after the specified generic identification,
with the actual pullback of the integral source-torus isomorphism. -/
theorem generic_comm :
    M.genericHom i ≫ (G.innerIso (A.genericPoint M)).hom =
      CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso A.torusIso).hom ≫
        M.genericHom i' := by
  have h := M.genericHom_comp_innerIso_of_isTransporter
    (CommGroupScheme.groupHom A.torusIso.hom ≫ i') i A.section_ A.isTransporter
  simpa only [genericPoint, IntegralModel.genericHom, Functor.map_comp,
    Functor.mapIso_hom, CommGroupScheme.baseChange, CommGroupScheme.groupHom,
    toMul_ofMul, Category.assoc] using h

/-- Inverting the same actual generic point reverses the conjugation square. -/
theorem inverse_generic_comm :
    M.genericHom i' ≫ (G.innerIso (A.genericPoint M)⁻¹).hom =
      CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso A.torusIso).inv ≫
        M.genericHom i := by
  rw [innerIso_inv_hom, Iso.comp_inv_eq, Category.assoc, A.generic_comm M,
    ← Category.assoc]
  change M.genericHom i' =
    CommGroupScheme.groupHom
      (((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso A.torusIso).inv ≫
        ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso A.torusIso).hom) ≫
      M.genericHom i'
  rw [Iso.inv_hom_id]
  exact (Category.id_comp _).symm

end SplitTorusConjugator

namespace IntegralModel

variable [HenselianLocalRing R]
  {k : Type u} [Field k] [Algebra R k]

/-- Construct actual integral conjugacy using maximality of the maps already
identified with the specified generic group of the model. -/
def henselianSplitTorusConjugator
    (hM : M.IsSmooth) (hk : Function.Surjective (algebraMap R k))
    (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj M.group).X.left]
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hiK : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T)
      (M.genericHom i))
    (hiK' : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T')
      (M.genericHom i')) : SplitTorusConjugator i i' :=
  Langlands.GroupScheme.henselianSplitTorusConjugator i i' hM hk
    (hG.of_iso M.genericIso) hT hT' hi hi'
    ((IsMaximalSplitTorus.comp_iso_iff _ M.genericIso).mp hiK)
    ((IsMaximalSplitTorus.comp_iso_iff _ M.genericIso).mp hiK')

end IntegralModel

end Langlands.GroupScheme
