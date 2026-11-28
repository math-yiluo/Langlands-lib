import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.Dynamic.DescentTransport
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.Reductive.StarActionScalarExtension
import Langlands.GroupScheme.Reductive.PinningFieldBaseChange
import Langlands.GroupScheme.Reductive.PinningGroupIsoTransport
import Langlands.GroupScheme.Reductive.PinningLattice
import Langlands.GroupScheme.SimplyConnected.TrivialStarInnerTwist
import Langlands.GroupScheme.Rational.ClassFunctionsTorusSeparationReduction
import Langlands.GroupScheme.Rational.GaloisSubgroupTowerTransport

/-! # Galois comparison for the parabolics of a split maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.GroupScheme.Dynamic StarActionIndependence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

namespace SplitTorusParabolicComparison

section Pullback

variable {B S U : Scheme.{u}} {b : S ⟶ B} {j : U ⟶ S} {r : U ⟶ B}
  (hr : j ≫ b = r) {a : S ⟶ S} {v : U ⟶ U}
  (ha : a ≫ b = b) (hv : v ≫ r = r) (h : j ≫ a = v ≫ j)

local notation "BC" => GroupScheme.baseChange

private def swapPullback (H : GroupScheme S) : (BC j).obj ((BC a).obj H) ≅
    (BC v).obj ((BC j).obj H) :=
  Descent.pullbackComparison a j (j ≫ a) rfl H ≪≫
    (Descent.pullbackComparison j v (j ≫ a) h.symm H).symm

private theorem swapPullback_naturality {H H' : GroupScheme S} (s : H ⟶ H') :
    (BC j).map ((BC a).map s) ≫ (swapPullback h H').hom =
      (swapPullback h H).hom ≫ (BC v).map ((BC j).map s) := by
  apply (cancel_mono (Descent.pullbackComparison j v (j ≫ a) h.symm H').hom).1
  simp only [swapPullback, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Descent.pullbackComparison_naturality_assoc]
  rw [Descent.pullbackComparison_naturality, Iso.inv_hom_id_assoc]

private theorem swapPullback_descent (G : GroupScheme B) :
    (BC j).map (descentBaseChangeIso b a ha G).hom ≫
        (Descent.pullbackComparison b j r hr G).hom =
      (swapPullback h ((BC b).obj G)).hom ≫
        (BC v).map (Descent.pullbackComparison b j r hr G).hom ≫
          (descentBaseChangeIso r v hv G).hom := by
  have hja : (j ≫ a) ≫ b = r := by rw [Category.assoc, ha, hr]
  change (BC j).map (Descent.pullbackComparison b a b ha G).hom ≫
      (Descent.pullbackComparison b j r hr G).hom =
    (swapPullback h ((BC b).obj G)).hom ≫
      (BC v).map (Descent.pullbackComparison b j r hr G).hom ≫
        (Descent.pullbackComparison r v r hv G).hom
  rw [pullbackComparison_tower b a b ha j (j ≫ a) r rfl hja hr,
    pullbackComparison_tower b j r hr v (j ≫ a) r h.symm hja hv]
  simp only [swapPullback, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

private theorem baseChangeCocharacter_swapPullback {H : GroupScheme S}
    (ν : (Gm S).toGrp ⟶ H) :
    baseChangeCocharacter j (baseChangeCocharacter a ν) ≫ (swapPullback h H).hom =
      baseChangeCocharacter v (baseChangeCocharacter j ν) := by
  apply (cancel_mono (Descent.pullbackComparison j v (j ≫ a) h.symm H).hom).1
  simp only [swapPullback, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, baseChangeCocharacter_tower]

variable {G : GroupScheme B} {T : CommGroupScheme S} (s : T.toGrp ⟶ (BC b).obj G)

private theorem swapPullback_inclusion :
    (BC j).map ((BC a).map s ≫ (descentBaseChangeIso b a ha G).hom) ≫
        (Descent.pullbackComparison b j r hr G).hom =
      (swapPullback h T.toGrp).hom ≫
        (BC v).map ((BC j).map s ≫ (Descent.pullbackComparison b j r hr G).hom) ≫
          (descentBaseChangeIso r v hv G).hom := by
  rw [Functor.map_comp, Category.assoc, swapPullback_descent hr ha hv h,
    ← Category.assoc, swapPullback_naturality, Functor.map_comp]
  simp only [Category.assoc]

private def swapTorus (T : CommGroupScheme S) :
    (CommGroupScheme.baseChange j).obj ((CommGroupScheme.baseChange a).obj T) ≅
      (CommGroupScheme.baseChange v).obj ((CommGroupScheme.baseChange j).obj T) :=
  CommGroupScheme.isoOfGroupIso (swapPullback h T.toGrp)

private theorem swapPullback_conjugatingPoint
    {c : Over.mk (𝟙 S) ⟶ ((BC b).obj G).X}
    {χ : (CommGroupScheme.baseChange a).obj T ≅ T}
    (hc : IsConjugatingPoint ((BC a).map s ≫ (descentBaseChangeIso b a ha G).hom) s c χ) :
    IsConjugatingPoint
      ((BC v).map ((BC j).map s ≫ (Descent.pullbackComparison b j r hr G).hom) ≫
        (descentBaseChangeIso r v hv G).hom)
      ((BC j).map s ≫ (Descent.pullbackComparison b j r hr G).hom)
      (baseChangeBasePoint j ((BC b).obj G) c ≫
        (Descent.pullbackComparison b j r hr G).hom.hom.hom)
      ((swapTorus h T).symm ≪≫ (CommGroupScheme.baseChange j).mapIso χ) := by
  let D := Descent.pullbackComparison b j r hr G
  have hsource :
      (BC j).map ((BC a).map s ≫ (descentBaseChangeIso b a ha G).hom) ≫ D.hom =
      CommGroupScheme.groupHom (swapTorus h T).hom ≫
        ((BC v).map ((BC j).map s ≫ D.hom) ≫ (descentBaseChangeIso r v hv G).hom) := by
    rw [← Category.assoc]
    exact swapPullback_inclusion hr ha hv h s
  have htarget : (BC j).map s ≫ D.hom =
      CommGroupScheme.groupHom (Iso.refl ((CommGroupScheme.baseChange j).obj T)).hom ≫
        ((BC j).map s ≫ D.hom) := (Category.id_comp _).symm
  simpa only [Iso.trans_refl] using
    (hc.baseChangeBasePoint j).transport (swapTorus h T) (Iso.refl _) D hsource htarget

private theorem cocharacter_baseChange_swap (ν : cocharacterLattice T) :
    cocharacterLattice.baseChange j ((CommGroupScheme.baseChange a).obj T)
      (cocharacterLattice.baseChange a T ν) ≫ (swapTorus h T).hom =
    cocharacterLattice.baseChange v ((CommGroupScheme.baseChange j).obj T)
      (cocharacterLattice.baseChange j T ν) :=
  congrArg Additive.ofMul (baseChangeCocharacter_swapPullback h (CommGroupScheme.groupHom ν))

private theorem cocharacter_baseChange_conjugators {C : CommGroupScheme U}
    (ν : cocharacterLattice T) (χ : (CommGroupScheme.baseChange a).obj T ≅ T)
    (φ : (CommGroupScheme.baseChange j).obj T ≅ C) :
    cocharacterLattice.baseChange j T (cocharacterLattice.baseChange a T ν ≫ χ.hom) ≫ φ.hom =
      cocharacterLattice.baseChange v ((CommGroupScheme.baseChange j).obj T)
        (cocharacterLattice.baseChange j T ν) ≫
        (((swapTorus h T).symm ≪≫ (CommGroupScheme.baseChange j).mapIso χ) ≪≫ φ).hom := by
  rw [cocharacterLattice.baseChange_comp, ← cocharacter_baseChange_swap h ν]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]

private theorem cocharacter_transport_along_iso {C : CommGroupScheme U} (P : CommGroupScheme B)
    (ν : cocharacterLattice C) (φ : C ≅ (CommGroupScheme.baseChange r).obj P) :
    cocharacterLattice.transport r v hv P (ν ≫ φ.hom) =
      cocharacterLattice.baseChange v C ν ≫ ((CommGroupScheme.baseChange v).mapIso φ ≪≫
        CommGroupScheme.descentBaseChangeIso r v hv P).hom := by
  change cocharacterLattice.baseChange v ((CommGroupScheme.baseChange r).obj P) (ν ≫ φ.hom) ≫
    (CommGroupScheme.descentBaseChangeIso r v hv P).hom = _
  simp only [cocharacterLattice.baseChange_comp, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]

private theorem transported_parabolic_of_conjugatingPoint
    {c : Over.mk (𝟙 S) ⟶ ((BC b).obj G).X}
    {χ : (CommGroupScheme.baseChange a).obj T ≅ T}
    (hc : IsConjugatingPoint ((BC a).map s ≫ (descentBaseChangeIso b a ha G).hom) s c χ)
    (ν : cocharacterLattice T) :
    SubgroupFunctor.descentTransport b a ha G (parabolic (CommGroupScheme.groupHom ν ≫ s)) =
      parabolic (CommGroupScheme.groupHom (cocharacterLattice.baseChange a T ν ≫ χ.hom) ≫
        s ≫ (((BC b).obj G).innerIso c⁻¹).hom) := by
  rw [← parabolic_transportCocharacter_eq_descentTransport]
  congr 1
  rw [innerIso_inv_hom, ← Category.assoc, Iso.eq_comp_inv]
  change baseChangeCocharacter a (CommGroupScheme.groupHom ν ≫ s) ≫
    (descentBaseChangeIso b a ha G).hom ≫ (((BC b).obj G).innerIso c).hom = _
  rw [baseChangeCocharacter_comp_hom, Category.assoc,
    ← Category.assoc ((BC a).map s), hc]
  rfl

private theorem conjugatingPoint_transport_target
    {C : CommGroupScheme U} {P : CommGroupScheme B}
    (i : C.toGrp ⟶ (BC r).obj G) (t : P.toGrp ⟶ G)
    {g : Over.mk (𝟙 U) ⟶ ((BC r).obj G).X}
    {φ : C ≅ (CommGroupScheme.baseChange r).obj P}
    (hg : IsConjugatingPoint i ((BC r).map t) g φ) :
    IsConjugatingPoint ((BC v).map i ≫ (descentBaseChangeIso r v hv G).hom) ((BC r).map t)
      (baseChangeBasePoint v ((BC r).obj G) g ≫ (descentBaseChangeIso r v hv G).hom.hom.hom)
      ((CommGroupScheme.baseChange v).mapIso φ ≪≫
        CommGroupScheme.descentBaseChangeIso r v hv P) := by
  have hi : (BC v).map i ≫ (descentBaseChangeIso r v hv G).hom =
      CommGroupScheme.groupHom (Iso.refl ((CommGroupScheme.baseChange v).obj C)).hom ≫
        ((BC v).map i ≫ (descentBaseChangeIso r v hv G).hom) := (Category.id_comp _).symm
  have hsymm : (Iso.refl ((CommGroupScheme.baseChange v).obj C)).symm =
      Iso.refl ((CommGroupScheme.baseChange v).obj C) := rfl
  simpa only [hsymm, Iso.refl_trans] using
    (hg.baseChangeBasePoint v).transport (Iso.refl _) (CommGroupScheme.descentBaseChangeIso r v hv P)
      (descentBaseChangeIso r v hv G) hi (descentBaseChangeIso_naturality r v hv t)

end Pullback

section Weyl

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)

private theorem exists_weyl_point (w : p.rootDatum.Aut) (hw : w ∈ p.rootDatum.weylGroup) :
    ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (ψ : p.torus ≅ p.torus),
      IsNormalizingPoint p.inclusion n ψ ∧
        ∀ ν : cocharacterLattice p.torus, w.coweightEquiv.symm ν = ν ≫ ψ.hom := by
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  have himage := (weylGroup k G p.isConnectedReductive p.torus p.isSplitTorus p.inclusion
    p.isMaximalTorus p.rootIndex p.rootDatum p.isRootDatum).1
  have hmem : RootPairing.Equiv.weightHom p.rootDatum w ∈ weylImage p.inclusion := by
    rw [himage]
    exact Subgroup.mem_map_of_mem _ hw
  obtain ⟨n, hn⟩ := MonoidHom.mem_range.1 hmem
  let ψ := normalizingAut p.inclusion n
  have hψ : (characterLattice.congr ψ).toIntLinearEquiv = w.weightEquiv := by
    ext χ
    exact DFunLike.congr_fun hn χ
  have hco := p.cocharacter_congr_eq_of_character_congr p w ψ hψ
  exact ⟨n.val, ψ, isNormalizingPoint_normalizingAut p.inclusion n,
    fun ν => (DFunLike.congr_fun hco ν).symm⟩

private theorem exists_weyl_of_two_conjugators {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {t : T.toGrp ⟶ G} {g g' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {β κ : T ≅ p.torus}
    (hg : IsConjugatingPoint t p.inclusion g β)
    (hg' : IsConjugatingPoint t p.inclusion g' κ) :
    ∃ w ∈ p.rootDatum.weylGroup, ∀ ν : cocharacterLattice T,
      w.coweightEquiv.symm (ν ≫ β.hom) = ν ≫ κ.hom := by
  have hn : IsNormalizingPoint p.inclusion (g' * g⁻¹) (β.symm ≪≫ κ) := hg.inv.mul hg'
  obtain ⟨w, hw, hwχ⟩ := exists_weyl_of_isNormalizingPoint p hn
  have hwco := p.cocharacter_congr_eq_of_character_congr p w (β.symm ≪≫ κ)
    (LinearEquiv.ext fun x => (hwχ x).symm)
  refine ⟨w, hw, fun ν => ?_⟩
  rw [← DFunLike.congr_fun hwco]
  change (ν ≫ β.hom) ≫ β.inv ≫ κ.hom = ν ≫ κ.hom
  rw [Category.assoc, Iso.hom_inv_id_assoc]

end Weyl

section Fields

variable {F K E : Type u} [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
  {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom]

local notation "b" => algebraBaseMap F K
local notation "j" => algebraBaseMap K E
local notation "r" => algebraBaseMap F E
local notation "MK" => Functor.obj (GroupScheme.baseChange b) M
local notation "ME" => Functor.obj (GroupScheme.baseChange r) M

local instance fieldBaseChangeAffine {k l : Type u} [Field k] [Field l] [Algebra k l]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k l)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k l))
  infer_instance

local notation "D" => Descent.pullbackComparison b j r Lie.algebraBaseMap_tower M

private theorem exists_conjugating_comparison (q : SplitPinning MK)
    (p : GaloisPinningData F E M) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶ (ME).X)
      (φ : (CommGroupScheme.baseChange j).obj q.torus ≅ p.toSplitPinning.torus)
      (e : RootPairing.Equiv q.rootDatum p.toSplitPinning.rootDatum),
      IsConjugatingPoint ((GroupScheme.baseChange j).map q.inclusion ≫ (D).hom)
        p.toSplitPinning.inclusion g φ ∧
      ∀ ν : cocharacterLattice q.torus,
        e.coweightEquiv.symm ν = cocharacterLattice.baseChange j q.torus ν ≫ φ.hom := by
  let qE := (q.baseChangeField (K := E)).mapGroupIso D
  obtain ⟨g, φ, hg⟩ := exists_conj qE p.toSplitPinning
  obtain ⟨eE, -, heE⟩ := exists_rootDatumEquiv_of_torusCompatibleIso
    qE.isConnectedReductive p.isConnectedReductive qE.isSplitTorus p.isSplitTorus
    qE.isMaximalTorus p.isMaximalTorus ((ME).innerIso g) φ hg qE.isRootDatum p.isRootDatum
  let e₀ : RootPairing.Equiv q.rootDatum qE.rootDatum := q.baseChangeRootDatumEquiv (F := E)
  let e : RootPairing.Equiv q.rootDatum p.rootDatum := eE.symm.comp e₀
  refine ⟨g, φ, e, hg, fun ν => (LinearEquiv.symm_apply_eq e.coweightEquiv).2 ?_⟩
  change ν = e₀.coweightEquiv (eE.coweightEquiv.symm
    (cocharacterLattice.baseChange j q.torus ν ≫ φ.hom))
  rw [← heE, RootPairing.Equiv.coweightEquiv_symm_coweightMap]
  exact (cocharacterLattice.baseChangeEquiv j q.torus q.isSplitTorus).symm_apply_apply ν |>.symm

omit [Algebra K E] [IsScalarTower F K E] in
private theorem exists_parabolic_weyl_conjugator (q : SplitPinning MK)
    (p : GaloisPinningData F E M)
    (e : RootPairing.Equiv q.rootDatum p.toSplitPinning.rootDatum)
    (w : p.toSplitPinning.rootDatum.Aut) (hw : w ∈ p.toSplitPinning.rootDatum.weylGroup) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (MK).X,
      ∀ ν : cocharacterLattice q.torus,
        parabolic (CommGroupScheme.groupHom
          (e.coweightEquiv (w.coweightEquiv.symm (e.coweightEquiv.symm ν))) ≫ q.inclusion) =
        parabolic (CommGroupScheme.groupHom ν ≫ q.inclusion ≫ ((MK).innerIso n).hom) := by
  let x := conjAut e.symm w
  obtain ⟨n, ψ, hn, hψ⟩ := exists_weyl_point q x (conjAut_mem_weylGroup e.symm hw)
  refine ⟨n, fun ν => ?_⟩
  have h : x.coweightEquiv.symm ν =
      e.coweightEquiv (w.coweightEquiv.symm (e.coweightEquiv.symm ν)) := by
    apply (LinearEquiv.symm_apply_eq x.coweightEquiv).2
    change ν = (e.symm.symm).coweightEquiv
      (w.coweightEquiv ((e.symm).coweightEquiv
        (e.coweightEquiv (w.coweightEquiv.symm (e.coweightEquiv.symm ν)))))
    have hs : (e.symm).coweightEquiv = e.coweightEquiv.symm :=
      LinearEquiv.ext fun _ => rfl
    have hss : (e.symm.symm).coweightEquiv = (e.symm).coweightEquiv.symm :=
      LinearEquiv.ext fun _ => rfl
    rw [hss, hs, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  rw [← h, hψ]
  change parabolic ((CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom ψ.hom) ≫
    q.inclusion) = _
  rw [Category.assoc, ← hn]

private theorem exists_parabolic_galois_conjugator (q : SplitPinning MK)
    (p : GaloisPinningData F E M)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶ (ME).X}
    {φ : (CommGroupScheme.baseChange j).obj q.torus ≅ p.toSplitPinning.torus}
    (hg : IsConjugatingPoint ((GroupScheme.baseChange j).map q.inclusion ≫ (D).hom)
      p.toSplitPinning.inclusion g φ)
    {e : RootPairing.Equiv q.rootDatum p.toSplitPinning.rootDatum}
    (he : ∀ ν : cocharacterLattice q.torus,
      e.coweightEquiv.symm ν = cocharacterLattice.baseChange j q.torus ν ≫ φ.hom)
    (σ : K ≃ₐ[F] K) (τ : E ≃ₐ[F] E)
    (h : j ≫ galoisBaseMap F K σ = galoisBaseMap F E τ ≫ j) :
    ∃ (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (MK).X)
      (w : p.toSplitPinning.rootDatum.Aut), w ∈ p.toSplitPinning.rootDatum.weylGroup ∧
      ∀ ν : cocharacterLattice q.torus,
        SubgroupFunctor.galoisTransport F K M σ
          (parabolic (CommGroupScheme.groupHom ν ≫ q.inclusion)) =
        parabolic (CommGroupScheme.groupHom
          (e.coweightEquiv (w.coweightEquiv.symm
            (cocharacterLattice.galoisRepresentation F E p.torus τ
              (e.coweightEquiv.symm ν)))) ≫ q.inclusion ≫ ((MK).innerIso c).hom) := by
  let a := galoisBaseMap F K σ
  let v := galoisBaseMap F E τ
  have ha : a ≫ b = b := galoisBaseMap_over F K σ
  have hv : v ≫ r = r := galoisBaseMap_over F E τ
  let δK := descentBaseChangeIso b a ha M
  let sK : ((CommGroupScheme.baseChange a).obj q.torus).toGrp ⟶ MK :=
    (GroupScheme.baseChange a).map q.inclusion ≫ δK.hom
  have := q.isConnectedReductive.smooth
  have := q.isConnectedReductive.connectedSpace
  have hmax : IsMaximalTorus sK := by
    let : Algebra K K := σ.toRingHom.toAlgebra
    have hbase := (maximalTorusBaseChange K K (MK) q.torus q.inclusion
      q.isMaximalTorus.1 q.isMaximalTorus.2.1).mp q.isMaximalTorus
    exact hbase.comp_iso δK
  obtain ⟨c, χ₀, hc₀⟩ := smoothMaximalSplitTorusConjugacy K (MK) _ _ sK q.inclusion
    (hmax.isMaximalSplitTorus (IsSplitTorus.baseChange a q.isSplitTorus))
    (q.isMaximalTorus.isMaximalSplitTorus q.isSplitTorus)
  let χ := CommGroupScheme.isoOfGroupIso χ₀
  have hc : IsConjugatingPoint sK q.inclusion c χ := hc₀
  let α := swapTorus h q.torus
  let β := (CommGroupScheme.baseChange v).mapIso φ ≪≫
    CommGroupScheme.descentBaseChangeIso r v hv p.torus
  let κ := (α.symm ≪≫ (CommGroupScheme.baseChange j).mapIso χ) ≪≫ φ
  have h₁ := (swapPullback_conjugatingPoint Lie.algebraBaseMap_tower ha hv h q.inclusion hc).mul hg
  have h₂ := conjugatingPoint_transport_target hv _ p.inclusion hg
  obtain ⟨w, hw, hwν⟩ := exists_weyl_of_two_conjugators p.toSplitPinning h₂ h₁
  refine ⟨c⁻¹, w, hw, fun ν => ?_⟩
  let transportedCochar : cocharacterLattice q.torus :=
    cocharacterLattice.baseChange a q.torus ν ≫ χ.hom
  let pulledCochar := cocharacterLattice.baseChange v
    ((CommGroupScheme.baseChange j).obj q.torus) (cocharacterLattice.baseChange j q.torus ν)
  have hleft : e.coweightEquiv.symm transportedCochar = pulledCochar ≫ κ.hom := by
    exact (he transportedCochar).trans (cocharacter_baseChange_conjugators h ν χ φ)
  have hright : cocharacterLattice.galoisRepresentation F E p.torus τ
      (e.coweightEquiv.symm ν) = pulledCochar ≫ β.hom := by
    exact (congrArg (cocharacterLattice.galoisRepresentation F E p.torus τ) (he ν)).trans
      (cocharacter_transport_along_iso hv p.torus (cocharacterLattice.baseChange j q.torus ν) φ)
  have hcochar : transportedCochar = e.coweightEquiv (w.coweightEquiv.symm
      (cocharacterLattice.galoisRepresentation F E p.torus τ (e.coweightEquiv.symm ν))) := by
    apply (LinearEquiv.symm_apply_eq e.coweightEquiv).1
    rw [hleft, hright]
    exact (hwν pulledCochar).symm
  rw [← hcochar]
  exact transported_parabolic_of_conjugatingPoint ha q.inclusion hc ν

/-- One root-datum comparison realizes Weyl conjugacy and Galois transport
of the cocharacter parabolics by rational conjugators over the splitting field. -/
theorem exists_rootDatumEquiv_parabolic_galoisComparison
    (q : SplitPinning MK) (p : GaloisPinningData F E M) :
    ∃ e : RootPairing.Equiv q.rootDatum p.toSplitPinning.rootDatum,
      (∀ w : p.toSplitPinning.rootDatum.Aut, w ∈ p.toSplitPinning.rootDatum.weylGroup →
        ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (MK).X,
          ∀ ν : cocharacterLattice q.torus,
            parabolic (CommGroupScheme.groupHom
              (e.coweightEquiv (w.coweightEquiv.symm (e.coweightEquiv.symm ν))) ≫ q.inclusion) =
            parabolic (CommGroupScheme.groupHom ν ≫ q.inclusion ≫ ((MK).innerIso n).hom)) ∧
      (∀ (σ : K ≃ₐ[F] K) (τ : E ≃ₐ[F] E),
        j ≫ galoisBaseMap F K σ = galoisBaseMap F E τ ≫ j →
        ∃ (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (MK).X)
          (w : p.toSplitPinning.rootDatum.Aut), w ∈ p.toSplitPinning.rootDatum.weylGroup ∧
          ∀ ν : cocharacterLattice q.torus,
            SubgroupFunctor.galoisTransport F K M σ
              (parabolic (CommGroupScheme.groupHom ν ≫ q.inclusion)) =
            parabolic (CommGroupScheme.groupHom
              (e.coweightEquiv (w.coweightEquiv.symm
                (cocharacterLattice.galoisRepresentation F E p.torus τ
                  (e.coweightEquiv.symm ν)))) ≫ q.inclusion ≫ ((MK).innerIso c).hom)) := by
  obtain ⟨g, φ, e, hg, he⟩ := exists_conjugating_comparison q p
  exact ⟨e, exists_parabolic_weyl_conjugator q p e, exists_parabolic_galois_conjugator q p hg he⟩

variable [LocallyOfFiniteType M.X.hom]

local instance fieldBaseChangeFiniteType : LocallyOfFiniteType (MK).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd M.X.hom b)
  infer_instance

/-- The ordinary Galois action of a coefficient automorphism fixing a field
over which the group has a split maximal torus belongs to the Weyl group. -/
theorem galoisAction_mem_weyl_of_fixes
    (q : SplitPinning MK) (p : GaloisPinningData F E M) (τ : E ≃ₐ[F] E)
    (hτ : galoisBaseMap F E τ ≫ j = j) :
    p.galoisAction τ ∈ p.toSplitPinning.rootDatum.weylGroup := by
  have hfix (x : K) : τ (algebraMap K E x) = algebraMap K E x := by
    change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K E)) =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) at hτ
    rw [← Spec.map_comp] at hτ
    exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of E => f.hom x)
      (Spec.map_injective hτ)
  let τK : E ≃ₐ[K] E := { τ.toRingEquiv with commutes' := hfix }
  have hτK : τK.restrictScalars F = τ := by ext x; rfl
  let qE := q.baseChangeField (K := E)
  let qSplit : GaloisPinningData K E MK := {
    torus := q.torus
    inclusion := q.inclusion
    isConnectedReductive := qE.isConnectedReductive
    isSplitTorus := qE.isSplitTorus
    isMaximalTorus := qE.isMaximalTorus
    rootIndex := qE.rootIndex
    rootDatum := qE.rootDatum
    isRootDatum := qE.isRootDatum
    isReduced := qE.isReduced
    base := qE.base
    pinning := qE.pinning }
  have hq : qSplit.starAction τK = 1 := by
    apply (qSplit.starAction_eq_one_iff τK).mpr
    have hg : qSplit.galoisAction τK = 1 := by
      apply equiv_ext_of_weightMap
      intro χ
      rw [galoisAction_weightMap_apply]
      exact TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus
        q.torus q.isSplitTorus τK χ
    rw [hg]
    exact one_mem _
  let pK := p.scalarExtension (E := K)
  obtain ⟨_, _, e, _, _, _, he⟩ :=
    starActionIndependence K E MK qSplit pK.pinning
  have hpK : pK.pinning.starAction τK = 1 := by
    apply Subtype.ext
    apply equiv_ext_of_weightMap
    intro χ
    obtain ⟨χ₀, rfl⟩ := e.weightEquiv.surjective χ
    have hc := he τK
    rw [hq] at hc
    exact (congrArg (fun f => f.weightMap χ₀) hc).symm
  apply (p.starAction_eq_one_iff τ).mp
  apply Subtype.ext
  apply equiv_ext_of_weightMap
  intro χ
  have hc := pK.star_eq τK
  rw [hτK, hpK] at hc
  exact pK.rootEquiv.weightEquiv.injective (congrArg (fun f => f.weightMap χ) hc)

end Fields

end SplitTorusParabolicComparison

end Langlands.GroupScheme
