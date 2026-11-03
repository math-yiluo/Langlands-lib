import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.BaseChangeReflection

/-! # Maximal tori in an ambient torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

/-- The split-torus predicate implies commutativity of the group object. -/
theorem IsSplitTorus.isCommMonObj {S : Scheme.{u}} {G : GroupScheme S}
    (hG : IsSplitTorus G) : IsCommMonObj G.X := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro U
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (isoPointsEquiv e U).injective
  rw [map_mul, map_mul, mul_comm]

open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal in
/-- A faithfully flat quasi-compact base change reflects commutativity. -/
theorem isCommMonObj_of_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    [Surjective b] [Flat b] [QuasiCompact b] (G : GroupScheme S)
    (hG : IsCommMonObj ((GroupScheme.baseChange b).obj G).X) :
    IsCommMonObj G.X := by
  let F := Over.pullback b
  have : IsCommMonObj (F.obj G.X) := hG
  refine ⟨F.map_injective ?_⟩
  apply (cancel_epi (LaxMonoidal.μ F G.X G.X)).mp
  rw [Functor.map_comp, Functor.LaxBraided.braided_assoc,
    ← obj.μ_def, IsCommMonObj.mul_comm]

/-- Every torus, including a nonsplit torus, is a commutative group scheme. -/
theorem IsTorus.isCommMonObj {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsTorus G) :
    IsCommMonObj G.X := by
  obtain ⟨K, hK, aK, hs⟩ := hG
  let := hK
  let := aK
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k K
  let := hsurj
  let := hflat
  let := hqc
  exact isCommMonObj_of_baseChange _ G hs.isCommMonObj

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- In an ambient torus every maximal-torus inclusion is an isomorphism. -/
theorem IsMaximalTorus.isIso_of_torus {i : T.toGrp ⟶ G}
    (hi : IsMaximalTorus i) (hG : IsTorus G) : IsIso i := by
  let U : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { G with comm := hG.isCommMonObj }
  exact hi.2.2 U (𝟙 G) i hG (IsClosedSubgroup.of_iso (Iso.refl G))
    (Category.comp_id i)

/-- The source isomorphism between maximal tori in an ambient torus. -/
def IsMaximalTorus.isoOverTorus {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (hG : IsTorus G) :
    T.toGrp ≅ T'.toGrp :=
  letI := hi.isIso_of_torus hG
  letI := hi'.isIso_of_torus hG
  asIso i ≪≫ (asIso i').symm

@[simp]
theorem IsMaximalTorus.isoOverTorus_hom_comp
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (hG : IsTorus G) :
    (hi.isoOverTorus hi' hG).hom ≫ i' = i := by
  let := hi.isIso_of_torus hG
  let := hi'.isIso_of_torus hG
  simp [IsMaximalTorus.isoOverTorus]

/-- Any two maximal tori in a torus are conjugate by its identity rational point. -/
theorem IsTorus.maximalToriAreConjugate (hG : IsTorus G) :
    MaximalToriAreConjugate G := by
  intro T T' i i' hi hi'
  refine ⟨1, hi.isoOverTorus hi' hG, ?_⟩
  rw [innerIso_one_hom, Category.comp_id, hi.isoOverTorus_hom_comp hi' hG]

end Langlands.GroupScheme
