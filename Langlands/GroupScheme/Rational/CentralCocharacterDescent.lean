import Langlands.GroupScheme.Absolute.CocharacterDescentLattice
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CocharacterTransportNaturality
import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.GroupScheme.Rational.SplitComponentCocharacters

/-! # Descent of central cocharacter orbit sums -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

section Reflection

open scoped CategoryTheory.Obj

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  [(Over.pullback b).Faithful] {H G : GroupScheme S} {i : H ⟶ G}

/-- Faithful base change reflects centrality on every test scheme. -/
theorem IsCentral.of_faithful_baseChange
    (hi : IsCentral ((GroupScheme.baseChange b).map i)) : IsCentral i := by
  intro T x T' a y
  apply (Over.pullback b).map_injective
  rw [Functor.map_mul, Functor.map_mul]
  have h := commute_of_mem_center
    (hi ((Over.pullback b).obj T')
      ((Over.pullback b).map (a ≫ x))) ((Over.pullback b).map y)
  change Commute
    ((Over.pullback b).map (a ≫ x) ≫ (Over.pullback b).map i.hom.hom)
    ((Over.pullback b).map y) at h
  simpa only [Functor.map_comp, Category.assoc] using h.eq

end Reflection

section Transport

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S)
  (ha : a ≫ b = b) {G : GroupScheme B}

/-- Transport along a base endomorphism preserves central cocharacters. -/
theorem IsCentral.transportCocharacter
    {ν : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj G}
    (hν : IsCentral ν) :
    IsCentral (transportCocharacter b a ha G ν) := by
  exact ((hν.baseChange a).comp (Gm.baseChangeIso a).inv).comp_iso
    (descentBaseChangeIso b a ha G)

end Transport

section Galois

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))
  {M : GroupScheme (Spec (CommRingCat.of k))} (t : T.toGrp ⟶ M)

local notation "T_K" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T
local notation "t_K" =>
  CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) t

/-- The actual central cocharacter submodule is stable under the Galois action. -/
theorem centralCocharacters_galois_stable
    (ν : cocharacterLattice T_K) (hν : ν ∈ centralCocharacters t_K)
    (σ : K ≃ₐ[k] K) :
    cocharacterLattice.galoisRepresentation k K T σ ν ∈
      centralCocharacters t_K := by
  rw [mem_centralCocharacters] at hν ⊢
  rw [cocharacterLattice.galoisRepresentation_apply]
  change IsCentral
    (transportCocharacter (algebraBaseMap k K) _ _ T.toGrp
      (CommGroupScheme.groupHom ν) ≫ t_K)
  rw [← transportCocharacter_naturality]
  exact hν.transportCocharacter _ _ _

variable [Fintype (K ≃ₐ[k] K)]

/-- Summing every Galois translate preserves all-test centrality. -/
theorem centralCocharacters_galoisOrbitSum_mem
    (ν : cocharacterLattice T_K) (hν : ν ∈ centralCocharacters t_K) :
    CocharacterAveraging.galoisOrbitSum k K T ν ∈ centralCocharacters t_K := by
  classical
  apply Submodule.sum_mem
  intro σ _
  exact centralCocharacters_galois_stable k K T t ν hν σ

variable [FiniteDimensional k K] [IsGalois k K] [IsAffineHom T.X.hom]

/-- The descended orbit sum of a geometrically central cocharacter is central
over the original field. -/
theorem centralCocharacters_descendedOrbitSum_mem
    (ν : cocharacterLattice T_K) (hν : ν ∈ centralCocharacters t_K) :
    CocharacterAveraging.descendedOrbitSum k K T ν ∈ centralCocharacters t := by
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  apply IsCentral.of_faithful_baseChange (algebraBaseMap k K)
  have hsum := centralCocharacters_galoisOrbitSum_mem k K T t ν hν
  rw [← CocharacterAveraging.baseChange_descendedOrbitSum] at hsum
  have h := hsum.comp (Gm.baseChangeIso (algebraBaseMap k K)).hom
  simpa only [cocharacterLattice.groupHom_baseChange, Category.assoc,
    Iso.hom_inv_id_assoc, Functor.map_comp] using h

namespace CocharacterAveraging

/-- The integral central orbit sum, as a rational central cocharacter. -/
def descendedCentralOrbitSum (ν : centralCocharacters (T := T_K) t_K) :
    centralCocharacters t :=
  ⟨descendedOrbitSum k K T ν.val,
    centralCocharacters_descendedOrbitSum_mem k K T t ν.val ν.property⟩

/-- Extending the central orbit sum recovers the original integral Galois sum. -/
theorem baseChange_descendedCentralOrbitSum
    (ν : centralCocharacters (T := T_K) t_K) :
    cocharacterLattice.baseChange (algebraBaseMap k K) T
        (descendedCentralOrbitSum k K T t ν).val =
      galoisOrbitSum k K T ν.val :=
  baseChange_descendedOrbitSum k K T ν.val

end CocharacterAveraging

end Galois

section SplitComponent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom T.X.hom] [IsAffineHom M.X.hom]
  {t : T.toGrp ⟶ M} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a)

include ha in
/-- A geometrically central cocharacter has a descended orbit sum that factors
through every specified split component of the ambient group. -/
theorem IsSplitComponent.exists_factor_descendedCentralOrbitSum
    (ν : cocharacterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hν : ν ∈ centralCocharacters ((GroupScheme.baseChange (algebraBaseMap k K)).map t)) :
    ∃ g : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ A.toGrp,
      g ≫ a =
        CommGroupScheme.groupHom (CocharacterAveraging.descendedOrbitSum k K T ν) ≫ t :=
  ha.exists_factor isSplitTorus_gm
    (centralCocharacters_descendedOrbitSum_mem k K T t ν hν)

include ha in
/-- A character vanishing on the extended split component pairs trivially with
the orbit sum of every cocharacter central in the extended ambient group. -/
theorem IsSplitComponent.latticePairing_centralOrbitSum_eq_zero
    [Mono t.hom.hom.left] (f : A ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ t = a)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hχ : (CommGroupScheme.baseChange (algebraBaseMap k K)).map f ≫ χ = 0)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hν : ν ∈ centralCocharacters ((GroupScheme.baseChange (algebraBaseMap k K)).map t)) :
    latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ
        (CocharacterAveraging.galoisOrbitSum k K T ν) = 0 := by
  have hdesc := centralCocharacters_descendedOrbitSum_mem k K T t ν hν
  rw [← ha.range_cocharacterMapInt_eq_centralCocharacters f hf] at hdesc
  obtain ⟨ζ, hζ⟩ := hdesc
  rw [← CocharacterAveraging.baseChange_descendedOrbitSum, ← hζ]
  change gmEndEquiv K (((Gm.commBaseChangeIso (algebraBaseMap k K)).inv ≫
    (CommGroupScheme.baseChange (algebraBaseMap k K)).map (ζ ≫ f)) ≫ χ) = 0
  rw [Functor.map_comp, Category.assoc, Category.assoc, hχ,
    Limits.comp_zero, Limits.comp_zero, map_zero]

end SplitComponent

end Langlands.GroupScheme
