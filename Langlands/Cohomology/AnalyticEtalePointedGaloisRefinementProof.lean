import Langlands.Cohomology.AnalyticEtalePointedGaloisRefinementBridge
import Langlands.Geometry.Analytic.AnalyticEtaleFrameSlices
import Langlands.Geometry.Analytic.AnalyticFrameGaloisCover
import Langlands.Geometry.Analytic.AnalyticGaloisCoverComponents
import Langlands.Geometry.Analytic.FiniteEtaleGeometricFibres

/-! # Pointed Galois refinements by ordered frames -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Filter Set Topology TopologicalSpace
open AnalyticOpenBaseChange (base baseInclusion inclusion projection)

universe u v

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}

private theorem finite_geometricFibre_of_compact_slice
    {L : Type u} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
    (a : (localizedFieldPointFunctor L).obj X)
    {y : localizedSpaceFunctor.obj X} (ha : ((localizedFieldPointProjection L).app X a).down = y)
    (U : Opens (localizedSpaceFunctor.obj X)) (hy : y ∈ U)
    (hU : etale (projection U p)) (hc : IsCompact (localizedSpaceFunctor.map p ⁻¹' {y})) :
    Finite {x : (localizedFieldPointFunctor L).obj Y // (localizedFieldPointFunctor L).map p x = a} := by
  let D := AnalyticOpenBaseChange.domain U p
  let j := inclusion U p
  let g := j ≫ p
  have hg : etale g := by
    rw [show g = projection U p ≫ baseInclusion U from (AnalyticOpenBaseChange.projection_comp U p).symm]
    exact etale_comp hU (etaleOpenDomainStatement X U U.isOpen)
  have hpoint (x : localizedSpaceFunctor.obj (domainObj Y D)) :
      localizedSpaceFunctor.map g x = localizedSpaceFunctor.map p x.val := by
    simp only [g, j, Functor.map_comp, TopCat.comp_app, domainι_apply]
  have hfibre : Subtype.val (p := (· ∈ D.carrier)) '' (localizedSpaceFunctor.map g ⁻¹' {y}) =
      localizedSpaceFunctor.map p ⁻¹' {y} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hpoint x).symm.trans hx
    · intro hz
      have hzU : localizedSpaceFunctor.map p z ∈ U :=
        (congrArg (· ∈ U) (show localizedSpaceFunctor.map p z = y from hz)).mpr hy
      let x : localizedSpaceFunctor.obj (domainObj Y D) := ⟨z, hzU⟩
      exact ⟨x, (hpoint x).trans hz, rfl⟩
  have hc' : IsCompact (localizedSpaceFunctor.map g ⁻¹'
      {((localizedFieldPointProjection L).app X a).down}) := by
    rw [ha, IsEmbedding.subtypeVal.isCompact_iff, hfibre]
    exact hc
  let Φ := localizedFieldPointFunctor (K := K) L
  let := finiteEtaleGeometricFibre (K := K) L a hg hc'
  let mapFibre (x : {x : Φ.obj (domainObj Y D) // Φ.map g x = a}) :
      {x : Φ.obj Y // Φ.map p x = a} :=
    ⟨Φ.map j x.val, by rw [← Φ.map_comp_apply]; exact x.property⟩
  apply Finite.of_surjective mapFibre
  rintro ⟨x, hx⟩
  have hxU : ((localizedFieldPointProjection L).app Y x).down ∈ D.carrier := by
    change localizedSpaceFunctor.map p _ ∈ U
    rw [← localizedFieldPointProjection_map_down p x, hx, ha]
    exact hy
  obtain ⟨x', hx'⟩ := exists_fieldPoint_lift_domainι D x hxU
  have hx'g : Φ.map g x' = a := by rw [show g = j ≫ p from rfl, Φ.map_comp_apply, hx', hx]
  exact ⟨⟨x', hx'g⟩, Subtype.ext hx'⟩

private theorem exists_fullFrame_at_point
    (hp : quasiEtale p) (hY : IsCompactSpace Y)
    (S : Set (localizedSpaceFunctor.obj X)) [T2Space S]
    (hS : ∀ x, localizedSpaceFunctor.map p x ∈ S)
    {R : LocalizedCategory.{u, v, v} (K := K)} {r s : R ⟶ Y}
    (h : IsPullback r s p p) (U : Opens (localizedSpaceFunctor.obj X))
    (hU : etale (projection U p)) (w : localizedSpaceFunctor.obj Y)
    (hy : localizedSpaceFunctor.map p w ∈ U) :
    let P := CompactAnalyticFibrePower.of_quasiEtale.{u, v, u} hp hY S hS
    ∃ n, (∃ z ∈ (P n).distinctLocus h, localizedSpaceFunctor.map (P n).base z =
      localizedSpaceFunctor.map p w) ∧
      ∀ z ∈ (P (n + 1)).distinctLocus h, localizedSpaceFunctor.map (P (n + 1)).base z ≠
        localizedSpaceFunctor.map p w := by
  classical
  let y := localizedSpaceFunctor.map p w
  obtain ⟨L, _, _, _, _, _, a, ha⟩ := exists_algebraicallyClosed_fieldPoint X y
  let Φ := localizedFieldPointFunctor (K := K) L
  let F := {x : Φ.obj Y // Φ.map p x = a}
  let toS (x : localizedSpaceFunctor.obj Y) : S := ⟨localizedSpaceFunctor.map p x, hS x⟩
  let : CompactSpace (localizedSpaceFunctor.obj Y) := hY.1
  have hc : IsCompact (localizedSpaceFunctor.map p ⁻¹' {y}) := by
    have hs : localizedSpaceFunctor.map p ⁻¹' {y} = toS ⁻¹' {toS w} := by
      ext x
      change (localizedSpaceFunctor.map p x = y) ↔ toS x = toS w
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [hs]
    exact (isClosed_singleton.preimage
      ((localizedSpaceFunctor.map p).hom.continuous.subtype_mk _)).isCompact
  let : Finite F := finite_geometricFibre_of_compact_slice a ha U hy hU hc
  obtain ⟨b, _, hb⟩ := pointedFieldPointLift_of_quasiEtale hp a w ha.symm
  let : Nonempty F := ⟨⟨b, hb⟩⟩
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fintype.card_pos (α := F)))
  let e : Fin (n + 1) ≃ F := (Fintype.equivFinOfCardEq hn).symm
  let P := CompactAnalyticFibrePower.of_quasiEtale.{u, v, u} hp hY S hS
  refine ⟨n, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := (P n).exists_fieldPoint_lift L a (fun i => (e i).val) (fun i => (e i).property)
    have hzbase : Φ.map (P n).base z = a := by
      rw [← (P n).coord_base 0, Φ.map_comp_apply, hz]
      exact (e 0).property
    have hzmap := congrArg (fun t => ((localizedFieldPointProjection L).app X t).down) hzbase
    rw [localizedFieldPointProjection_map_down, ha] at hzmap
    refine ⟨_, ((P n).mem_distinctLocus_iff_fieldPoint_injective h hY hp L z).mpr ?_, hzmap⟩
    intro i j hij
    exact e.injective (Subtype.ext ((hz i).symm.trans (hij.trans (hz j))))
  · intro z hz hzbase
    obtain ⟨b', hb', hbbase⟩ := pointedFieldPointLift_of_quasiEtale (P (n + 1)).quasiEtale_base
      a z (hzbase.trans ha.symm)
    have hbij := ((P (n + 1)).mem_distinctLocus_iff_fieldPoint_injective h hY hp L b').mp
      (hb'.symm ▸ hz)
    let q (i : Fin (n + 1 + 1)) : F := ⟨Φ.map ((P (n + 1)).coord i) b', by
      rw [← Φ.map_comp_apply, (P (n + 1)).coord_base, hbbase]⟩
    have hq : Function.Injective q := fun _ _ heq => hbij (congrArg Subtype.val heq)
    have hcard := Fintype.card_le_of_injective q hq
    rw [Fintype.card_fin, hn] at hcard
    exact Nat.not_succ_le_self _ hcard

private theorem exists_fullFrame_open
    (hp : quasiEtale p) (hY : IsCompactSpace Y)
    {S : Set (localizedSpaceFunctor.obj X)} [T2Space S] (hSo : IsOpen S)
    (hS : ∀ x, localizedSpaceFunctor.map p x ∈ S)
    {R : LocalizedCategory.{u, v, v} (K := K)} {r s : R ⟶ Y}
    (h : IsPullback r s p p) (U : Opens (localizedSpaceFunctor.obj X))
    (hU : etale (projection U p)) {n : ℕ}
    (P : CompactAnalyticFibrePower.{u, v, u} p n)
    (Q : CompactAnalyticFibrePower.{u, v, u} p (n + 1))
    {y : localizedSpaceFunctor.obj X} (hyU : y ∈ U) (hyS : y ∈ S)
    (hex : ∃ z ∈ P.distinctLocus h, localizedSpaceFunctor.map P.base z = y)
    (hmax : ∀ z ∈ Q.distinctLocus h, localizedSpaceFunctor.map Q.base z ≠ y) :
    ∃ (V : Opens (localizedSpaceFunctor.obj X)), y ∈ V ∧
      etale (projection V p) ∧
      (∀ x ∈ V, ∃ z ∈ P.distinctLocus h, localizedSpaceFunctor.map P.base z = x) ∧
      ∀ z ∈ Q.distinctLocus h, localizedSpaceFunctor.map Q.base z ∉ V := by
  let A : Set (localizedSpaceFunctor.obj P.obj) :=
    localizedSpaceFunctor.map P.base ⁻¹' (U : Set (localizedSpaceFunctor.obj X))
  let B : Set (localizedSpaceFunctor.obj Q.obj) :=
    localizedSpaceFunctor.map Q.base ⁻¹' (U : Set (localizedSpaceFunctor.obj X))
  let g := projection U P.base ≫ baseInclusion U
  let F : Set (localizedSpaceFunctor.obj (AnalyticOpenBaseChange.obj U P.base)) :=
    {z | z.val ∈ P.distinctLocus h}
  have hg : etale g :=
    etale_comp (P.etale_openProjection hp hY S hS U hU) (etaleOpenDomainStatement X U U.isOpen)
  have hgpt (z : localizedSpaceFunctor.obj (AnalyticOpenBaseChange.obj U P.base)) :
      localizedSpaceFunctor.map g z = localizedSpaceFunctor.map P.base z.val := by
    rw [show g = inclusion U P.base ≫ P.base from AnalyticOpenBaseChange.projection_comp U P.base,
      Functor.map_comp, TopCat.comp_app, domainι_apply]
  have hF : IsOpen F :=
    (P.isDistinguishedOpen_distinctLocus h hY hp).1.preimage continuous_subtype_val
  let good := localizedSpaceFunctor.map g '' F
  have hgood : IsOpen good := etaleOpenMap K g hg _ hF
  let toS (z : localizedSpaceFunctor.obj Q.obj) : S :=
    ⟨localizedSpaceFunctor.map Q.base z, by
      rw [← Q.coord_base 0, Functor.map_comp, TopCat.comp_app]
      exact hS _⟩
  let bad := toS '' closure (B ∩ Q.distinctLocus h)
  let : CompactSpace (localizedSpaceFunctor.obj Q.obj) := Q.compact.1
  have hbad : IsClosed bad :=
    (isClosed_closure.isCompact.image
      ((localizedSpaceFunctor.map Q.base).hom.continuous.subtype_mk _)).isClosed
  have hrel : B ∩ closure (B ∩ Q.distinctLocus h) ⊆ Q.distinctLocus h :=
    isClosed_preimage_val.mp (Q.isClosed_distinctLocus_openSlice h U hU)
  let V : Opens (localizedSpaceFunctor.obj X) :=
    ⟨good ∩ Subtype.val '' badᶜ, hgood.inter (hSo.isOpenMap_subtype_val _ hbad.isOpen_compl)⟩
  have hVU : V ≤ U := by
    rintro x ⟨⟨z, _, rfl⟩, _⟩
    rw [hgpt]
    exact z.property
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · obtain ⟨z, hz, hzbase⟩ := hex
    have hzU : z ∈ A := (congrArg (· ∈ U) hzbase).mpr hyU
    refine ⟨⟨⟨z, hzU⟩, hz, (hgpt ⟨z, hzU⟩).trans hzbase⟩, ⟨⟨y, hyS⟩, ?_, rfl⟩⟩
    rintro ⟨x, hx, hxy⟩
    have hxy' : localizedSpaceFunctor.map Q.base x = y := congrArg Subtype.val hxy
    exact hmax x (hrel ⟨(congrArg (· ∈ U) hxy').mpr hyU, hx⟩) hxy'
  · have hi : etale (inclusion V p) :=
      etaleOpenDomainStatement Y _ (V.isOpen.preimage (localizedSpaceFunctor.map p).hom.continuous)
    let k : AnalyticOpenBaseChange.obj V p ⟶ AnalyticOpenBaseChange.obj U p :=
      domainOrderMap (fun _ hz => hVU hz)
    have hk : k ≫ inclusion U p = inclusion V p := domainOrderMap_comp_inclusion _
    have hke : etale k := etale_of_comp_domainι _ (hk.symm ▸ hi)
    apply etale_of_comp_domainι _
    change etale (projection V p ≫ baseInclusion V)
    rw [AnalyticOpenBaseChange.projection_comp, ← hk, Category.assoc,
      ← AnalyticOpenBaseChange.projection_comp]
    exact etale_comp hke (etale_comp hU (etaleOpenDomainStatement X U U.isOpen))
  · rintro x ⟨⟨z, hz, rfl⟩, _⟩
    exact ⟨z.val, hz, (hgpt z).symm⟩
  · intro z hz hV
    obtain ⟨x, hx, hxy⟩ := hV.2
    exact hx ⟨z, subset_closure ⟨hVU hV, hz⟩, Subtype.ext hxy.symm⟩

/-- Compact ordered frames give pointed relative Galois refinements of étale arrows. -/
theorem pointedAnalyticGaloisRefinement : PointedAnalyticGaloisRefinementStatement.{u, v} K := by
  intro W X f hf w
  let y := localizedSpaceFunctor.map f w
  obtain ⟨T, hT, hT₂⟩ := (presentationOf X).presentation.atlas.locallyHausdorff y
  let S := interior T
  let : T2Space T := hT₂
  let : T2Space S := (IsEmbedding.inclusion interior_subset).t2Space
  have hyS : y ∈ S := mem_interior_iff_mem_nhds.mpr hT
  obtain ⟨D, U, hD, hwD, hDS, hyU, hU⟩ :=
    compactEtaleNeighborhood (K := K) hf w (localizedSpaceFunctor.map f ⁻¹' S)
      ((localizedSpaceFunctor.map f).hom.continuous.continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hyS))
  let A := domainObj W D
  let p := domainι W D ≫ f
  let w' : localizedSpaceFunctor.obj A := ⟨w, hwD⟩
  have hp : quasiEtale p := quasiEtale_domainι_comp_of_etale D f hf
  have hpU : etale (projection U p) := etale_preimageOpenDomainMap_domainι_comp hf D U hU
  have hpS (z : localizedSpaceFunctor.obj A) : localizedSpaceFunctor.map p z ∈ S := by
    rw [show p = domainι W D ≫ f from rfl, Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact hDS z.property
  have hw' : localizedSpaceFunctor.map p w' = y := by
    rw [show p = domainι W D ≫ f from rfl, Functor.map_comp, TopCat.comp_app, domainι_apply]
  let R := localizedQuasiEtalePullback p p hp
  have hR := IsPullback.of_isLimit R.2
  let powers := CompactAnalyticFibrePower.of_quasiEtale.{u, v, u} hp hD S hpS
  obtain ⟨n, hsmall, hlarge⟩ := exists_fullFrame_at_point hp hD S hpS hR U hpU w' (hw'.symm ▸ hyU)
  let P := powers n
  let Q := powers (n + 1)
  obtain ⟨V, hyV, hpV, hsmallV, hlargeV⟩ :=
    exists_fullFrame_open hp hD isOpen_interior hpS hR U hpU P Q (y := y) hyU hyS
      (by simpa only [hw'] using hsmall) (by simpa only [hw'] using hlarge)
  let F := P.frameDomain hR hD hp V
  let P' := domainObj P.obj F
  let q := P.frameMap hR hD hp V
  let : T2Space (presentationOf P.obj).presentation.space := P.compact.2
  let : T2Space (localizedSpaceFunctor.obj P') :=
    inferInstanceAs (T2Space F.carrier)
  let C := P.frameGaloisCover hR hD hp V Q (P.etale_openProjection hp hD S hpS V hpV) hsmallV hlargeV
  let y' : localizedSpaceFunctor.obj (base V) := ⟨y, hyV⟩
  obtain ⟨z, hz⟩ := C.surjective y'
  let := localizedSpaceAction C.deck
  obtain ⟨O, hzO, _, _, _, hO⟩ := C.exists_distinguishedDeckComponent z ⊤ (by simp)
  let H := MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) z
  let E := (presentationOf P').openDomain (O : Set (localizedSpaceFunctor.obj P')) O.isOpen
  let V' := C.componentImage O
  let D₀ := (presentationOf X).openDomain (V : Set (localizedSpaceFunctor.obj X)) V.isOpen
  let D₁ := (presentationOf (base V)).openDomain (V' : Set (localizedSpaceFunctor.obj (base V))) V'.isOpen
  let B : Opens (localizedSpaceFunctor.obj X) :=
    ⟨Subtype.val '' (V' : Set (localizedSpaceFunctor.obj (base V))), V.isOpen.isOpenMap_subtype_val _ V'.isOpen⟩
  have heq : D₀.subspaceExtend D₁ =
      (presentationOf X).openDomain (B : Set (localizedSpaceFunctor.obj X)) B.isOpen := by
    ext x
    rfl
  let i : domainObj (base V) D₁ ≅ domainObj X (D₀.subspaceExtend D₁) :=
    domainNestedLocalizationIso (presentationOf X) D₀ D₁
  let j : domainObj X (D₀.subspaceExtend D₁) ≅ base B :=
    eqToIso (congrArg (domainObj X) heq)
  let e := i ≪≫ j
  have hj : j.hom ≫ baseInclusion B = domainι X (D₀.subspaceExtend D₁) :=
    eqToIso_hom_domainInclusion (presentationOf X) heq
  have he : e.hom ≫ baseInclusion B = domainι (base V) D₁ ≫ baseInclusion V := calc
    _ = i.hom ≫ (j.hom ≫ baseInclusion B) := Category.assoc _ _ _
    _ = i.hom ≫ domainι X (D₀.subspaceExtend D₁) := congrArg (i.hom ≫ ·) hj
    _ = _ := domainNestedLocalizationIso_hom_inclusion (presentationOf X) D₀ D₁
  let m := C.componentMap O ≫ e.hom
  have hm : m ≫ baseInclusion B = domainι P' E ≫ q ≫ baseInclusion V := by
    rw [show m = C.componentMap O ≫ e.hom from rfl, Category.assoc, he, ← Category.assoc,
      C.componentMap_comp, Category.assoc]
  have hmpt (x : localizedSpaceFunctor.obj (domainObj P' E)) :
      (localizedSpaceFunctor.map m x).val = (localizedSpaceFunctor.map q x.val).val := by
    simpa only [Functor.map_comp, TopCat.comp_app, domainι_apply] using
      congrArg (fun k => localizedSpaceFunctor.map k x) hm
  have hyB : y ∈ B := ⟨y', ⟨z, hzO, hz⟩, rfl⟩
  let z' : localizedSpaceFunctor.obj (domainObj P' E) := ⟨z, hzO⟩
  refine ⟨{
    baseOpen := B
    mem_baseOpen := hyB
    source := domainObj P' E
    Γ := H
    p := m
    geometry := (C.restrictComponent O H hO).postcompIso e
    lift := domainι P' E ≫ domainι P.obj F ≫ P.coord 0 ≫ domainι W D
    factors := ?_
    point := z'
    map_point := Subtype.ext ((hmpt z').trans (congrArg Subtype.val hz))
    unique_point := ?_ }⟩
  · rw [hm, show q ≫ baseInclusion V = domainι P.obj F ≫ P.base from P.frameMap_comp hR hD hp V]
    simp only [Category.assoc, ← show p = domainι W D ≫ f from rfl, P.coord_base]
  · intro x hx
    apply Subtype.ext
    apply C.eq_of_mem_stabilizerComponent O hzO x.property _ hO
    exact Subtype.ext ((congrArg Subtype.val hz).trans
      ((congrArg Subtype.val hx).symm.trans (hmpt x)))

end Langlands.Analytic.SaturatedAtlasPresentation
