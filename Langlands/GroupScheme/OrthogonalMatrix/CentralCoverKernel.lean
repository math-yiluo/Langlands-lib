import Langlands.GroupScheme.OrthogonalMatrix.CentralCoverLattice
import Langlands.GroupScheme.Quaternionic.SpinKernelTorus
import Langlands.GroupScheme.CentralIsogeny.MaximalTorusFactor
import Langlands.GroupScheme.CentralIsogeny.IndexTwoKernel
import Langlands.GroupScheme.CentralIsogeny.SplitMaximalTorusLiftProof

/-! # A specified cocharacter generates the kernel of an even orthogonal cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)
local notation "𝐆" => identityComponent (groupScheme l (CommRingCat.of k))

section CompatibleTorus

variable {S : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : S ⟶ identityComponent (groupScheme l (CommRingCat.of k))}
  (hp : IsCentralIsogeny p) (hS : IsSimplyConnected S) (hT : IsSplitTorus T.toGrp)
  {i : T.toGrp ⟶ S} (hi : IsMaximalTorus i)
  (t : T ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l))
  (ht : i ≫ p = CommGroupScheme.groupHom t ≫ identityTorus l k)
  (hl : 3 ≤ Fintype.card l)
  (c : cocharacterLattice T) (i₀ : l)
  (hc : GeneralLinear.cocharacterCoordEquiv l k (c ≫ t) = Pi.single i₀ 2)

include hp hS hT hi ht hl hc

/-- The actual cocharacter range supplies the even-image hypotheses for the specified
preimage of `2 eᵢ₀`. -/
theorem centralCoverEvenImage : Quaternionic.SpinKernelTorus.EvenImage T t c i₀ := by
  have : Nontrivial l := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hr := range_cocharacterCoord_eq_pairLattice hp hS hT hi t ht hl
  refine ⟨hp.cocharacterMapInt_injective_of_square hi.2.1
    (isClosedSubgroup_identityTorus l k) t ht, ?_, ?_, hc⟩
  · intro ν
    apply (TypeDParityLattice.mem_pairLattice_iff _).mp
    rw [← hr]
    exact ⟨ν, rfl⟩
  · intro j
    have hj := TypeDParityLattice.single_sub_single_mem j i₀
    rw [← hr] at hj
    exact hj

/-- The specified primitive cocharacter is injective on points of every test scheme. -/
theorem centralCoverCocharacter_comp_injective {U : Over (Spec (CommRingCat.of k))} :
    Function.Injective fun u : U ⟶ (Gm (Spec (CommRingCat.of k))).X =>
      u ≫ (CommGroupScheme.groupHom c).hom.hom ≫ i.hom.hom := by
  have := hi.2.1.mono_overHom
  intro u v huv
  apply (centralCoverEvenImage hp hS hT hi t ht hl c i₀ hc).comp_injective hT
  exact (cancel_mono i.hom.hom).mp huv

/-- Every ambient kernel point has a unique square-root parameter under `c`. -/
theorem existsUnique_kernel_comp_eq {U : Over (Spec (CommRingCat.of k))}
    (x : U ⟶ S.X) (hx : x ≫ p.hom.hom = 1) :
    ∃! u : U ⟶ (Gm (Spec (CommRingCat.of k))).X,
      u * u = 1 ∧ u ≫ (CommGroupScheme.groupHom c).hom.hom ≫ i.hom.hom = x := by
  obtain ⟨y, hy⟩ := (IndexTwoKernel.kernelPointsMap_bijective hp
    hS.isSemisimple.isConnectedReductive hi (isClosedSubgroup_identityTorus l k) ht U).2
      ⟨x, hx⟩
  have hy' : y.val ≫ i.hom.hom = x := congrArg Subtype.val hy
  obtain ⟨u, hu, huc⟩ :=
    (centralCoverEvenImage hp hS hT hi t ht hl c i₀ hc).exists_comp_eq hT y.val y.2
  have hui : u ≫ (CommGroupScheme.groupHom c).hom.hom ≫ i.hom.hom = x := by
    rw [← Category.assoc, huc, hy']
  refine ⟨u, ⟨hu, hui⟩, ?_⟩
  intro v hv
  exact centralCoverCocharacter_comp_injective hp hS hT hi t ht hl c i₀ hc
    (hv.2.trans hui.symm)

end CompatibleTorus

section LiftedCocharacter

variable {S : GroupScheme (Spec (CommRingCat.of k))}
  {p : S ⟶ identityComponent (groupScheme l (CommRingCat.of k))}
  (hp : IsCentralIsogeny p) (hS : IsSimplyConnected S)
  (hl : 3 ≤ Fintype.card l)
  (a : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ S)
  (b : cocharacterLattice
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)))
  (ha : a ≫ p = CommGroupScheme.groupHom b ≫ identityTorus l k)
  (i₀ : l) (hb : GeneralLinear.cocharacterCoordEquiv l k b = Pi.single i₀ 2)

include hp hS hl ha hb

/-- A lift of the coordinate cocharacter `2 eᵢ₀` generates the entire kernel, with unique
square-root parameter, on every test scheme. A compatible source torus is constructed. -/
theorem existsUnique_kernel_lift_comp_eq {U : Over (Spec (CommRingCat.of k))}
    (x : U ⟶ S.X) (hx : x ≫ p.hom.hom = 1) :
    ∃! u : U ⟶ (Gm (Spec (CommRingCat.of k))).X,
      u * u = 1 ∧ u ≫ a.hom.hom = x := by
  have : Nontrivial l := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let hG := hS.isSemisimple.isConnectedReductive
  obtain ⟨T, i, t, hT, hi, ht⟩ := centralIsogenySplitMaximalTorusLift k S 𝐆
    hG (isConnectedReductive_identityComponent l k) p hp 𝔻 (identityTorus l k)
      (SymplecticMatrix.isSplitTorus_diagonalTorus l k) (isMaximalTorus_identityTorus l k)
  let c := hp.maximalTorusFactor hG hi t ht a b ha
  have hc : GeneralLinear.cocharacterCoordEquiv l k (c ≫ t) = Pi.single i₀ 2 := by
    rw [IsCentralIsogeny.maximalTorusFactor_comp_t, hb]
    exact isClosedSubgroup_identityTorus l k
  have hci : (CommGroupScheme.groupHom c).hom.hom ≫ i.hom.hom = a.hom.hom :=
    congrArg (fun f => f.hom.hom) (hp.maximalTorusFactor_comp hG hi t ht a b ha)
  simpa only [hci] using existsUnique_kernel_comp_eq hp hS hT hi t ht hl c i₀ hc x hx

omit hp hS hl in
/-- Every square-root parameter maps into the ambient kernel. -/
theorem liftedCocharacter_comp_eq_one {U : Over (Spec (CommRingCat.of k))}
    (u : U ⟶ (Gm (Spec (CommRingCat.of k))).X) (hu : u * u = 1) :
    (u ≫ a.hom.hom) ≫ p.hom.hom = 1 := by
  have hb' : b = (2 : ℤ) • (GeneralLinear.cocharacterCoordEquiv l k).symm
      (Pi.single i₀ 1) := by
    apply (GeneralLinear.cocharacterCoordEquiv l k).injective
    rw [hb, map_zsmul, LinearEquiv.apply_symm_apply]
    ext j
    simp [Pi.single_apply]
  have hub : u ≫ (CommGroupScheme.groupHom b).hom.hom = 1 := by
    rw [hb', comp_groupHom_zsmul, zpow_two, ← MonObj.mul_comp, hu, MonObj.one_comp]
  exact IndexTwoKernel.comp_comp_eq_one ha hub

/-- The specified lifted cocharacter identifies square roots of unity with the full
ambient kernel on every relative test scheme. -/
def kernelPointsEquiv (U : Over (Spec (CommRingCat.of k))) :
    {u : U ⟶ (Gm (Spec (CommRingCat.of k))).X // u * u = 1} ≃
      {x : U ⟶ S.X // x ≫ p.hom.hom = 1} :=
  Equiv.ofBijective
    (fun u => ⟨u.val ≫ a.hom.hom, liftedCocharacter_comp_eq_one a b ha i₀ hb u.val u.2⟩)
    (by
      constructor
      · intro u v huv
        obtain ⟨w, hw, huniq⟩ :=
          existsUnique_kernel_lift_comp_eq hp hS hl a b ha i₀ hb
            (u.val ≫ a.hom.hom) (liftedCocharacter_comp_eq_one a b ha i₀ hb u.val u.2)
        apply Subtype.ext
        exact (huniq u.val ⟨u.2, rfl⟩).trans
          (huniq v.val ⟨v.2, (congrArg Subtype.val huv).symm⟩).symm
      · intro x
        obtain ⟨u, hu, -⟩ := existsUnique_kernel_lift_comp_eq hp hS hl a b ha i₀ hb x.val x.2
        exact ⟨⟨u, hu.1⟩, Subtype.ext hu.2⟩)

@[simp]
theorem kernelPointsEquiv_apply_val (U : Over (Spec (CommRingCat.of k)))
    (u : {u : U ⟶ (Gm (Spec (CommRingCat.of k))).X // u * u = 1}) :
    (kernelPointsEquiv hp hS hl a b ha i₀ hb U u).val = u.val ≫ a.hom.hom := rfl

end LiftedCocharacter

end Langlands.GroupScheme.OrthogonalMatrix
