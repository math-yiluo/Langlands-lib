/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation
public import WeilConjectures.WeilSheaf.DirectImageRestriction
public import WeilConjectures.WeilSheaf.LisseExtension
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.RealPurity

/-!
# Lisse Weil sheaves with trivial inertia at a boundary point

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field, `U₀` geometrically connected, and `z ∈ C₀ ∖ U₀` a boundary point with inertia group
`I_z ⊆ W(U₀)` (`AlgebraicGeometry.WeilGroup.boundaryInertia`). A lisse representation of `W(U₀)`
which is trivial on `I_z` is trivial on the whole kernel of `π₁(U₀) → π₁(U₀ ∪ {z})`, intersected
with the Weil group (`AlgebraicGeometry.WeilGroup.apply_eq_self_of_mem_weilLocalKernel`): its
kernel on the geometric part is closed and normal, so its image in `π₁(U₀)` is a closed normal
subgroup (by the density of the Weil group) containing the inertia group, hence the closed normal
subgroup it generates, which is the local kernel
(`AlgebraicGeometry.WeilGroup.localKernel_le_topologicalClosure_normalClosure`).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] [Smooth p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]
  [GeometricallyConnected pU] [ConnectedSpace U] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
  [IsIntegral C] [SmoothOfRelativeDimension 1 p] (hj : j ≫ p = pU)
  (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]
  (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V]

include hj τ GC in
/-- **A lisse representation trivial on inertia is trivial on the local kernel.** Let `ρ` be a
lisse representation of `W(U₀)` on which the inertia group `I_z` at a boundary point `z` acts
trivially. Then every element of `W(U₀)` of degree zero acting trivially on the covers of `U₀`
which extend over `z` (`AlgebraicGeometry.WeilGroup.weilLocalKernel`) acts trivially through `ρ`.

The elements of the geometric part acting trivially form a closed normal subgroup `N` of
`W(U₀)`, since `ρ` is continuous on the geometric part. Its image in `π₁(U₀)` is compact, hence
closed, and normal since the Weil group is dense; it contains the inertia group, hence the local
kernel (`AlgebraicGeometry.WeilGroup.localKernel_le_topologicalClosure_normalClosure`).
(blueprint: `corollary-unramified-boundary-point--2`) -/
theorem apply_eq_self_of_mem_weilLocalKernel
    {ρ : Representation (PadicAlgCl l) (weilGroup pU sU GU) V}
    (hρ : (ofFundamentalGroup pU sU GU).IsLisse l ρ) (z : ↥((Set.range j.base)ᶜ))
    (hI : ∀ g ∈ boundaryInertia (p := p) (pU := pU) j sU GU z, ∀ v, ρ g v = v)
    {w : weilGroup pU sU GU} (hw : w ∈ weilLocalKernel (p := p) (pU := pU) j sU GU z.1)
    (v : V) : ρ w v = v := by
  have hcU : ∀ P, ContinuousSMul GU ((fiber sU).obj P) := fun P ↦
    IsFundamentalGroup.continuous_smul P
  have : T2Space GU := (toAutHomeo (fiber sU) GU).isEmbedding.t2Space
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace pU
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated pU
  let φ : weilGroup pU sU GU →* GU := (MonoidHom.fst _ _).comp (weilGroup pU sU GU).subtype
  -- the elements of the geometric part acting trivially
  let N : Subgroup (weilGroup pU sU GU) := ρ.asGroupHom.ker ⊓ (weilGroupDeg pU sU GU).ker
  have hNmem (g : weilGroup pU sU GU) :
      g ∈ N ↔ (∀ v, ρ g v = v) ∧ g ∈ (weilGroupDeg pU sU GU).ker := by
    refine and_congr_left' ⟨fun h v ↦ ?_, fun h ↦ MonoidHom.mem_ker.2 (Units.ext ?_)⟩
    · have h' := congrArg (fun u : (Module.End (PadicAlgCl l) V)ˣ ↦ u.1 v)
        (MonoidHom.mem_ker.1 h)
      simpa [Representation.asGroupHom_apply] using h'
    · rw [Representation.asGroupHom_apply]
      exact LinearMap.ext h
  -- `N` is the image of a closed subset of the compact geometric part
  have hK : CompactSpace (weilGroupDeg pU sU GU).ker :=
    isCompact_iff_compactSpace.mp (isCompact_ker_weilGroupDeg pU sU GU)
  let b := Module.finBasis (PadicAlgCl l) V
  let T : Set (weilGroupDeg pU sU GU).ker := {g | ∀ i i', LinearMap.toMatrix b b (ρ g) i i' =
    LinearMap.toMatrix b b 1 i i'}
  have hT : IsClosed T := by
    simp only [T, Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun i' ↦
      isClosed_eq (hρ.continuous_toMatrix b i i') continuous_const
  have hNT : (N : Set (weilGroup pU sU GU)) = Subtype.val '' T := by
    ext g
    refine ⟨fun hg ↦ ⟨⟨g, ((hNmem g).1 hg).2⟩, fun i i' ↦ ?_, rfl⟩, ?_⟩
    · have h1 : ρ g = 1 := LinearMap.ext fun v ↦
        (((hNmem g).1 hg).1 v).trans (Module.End.one_apply v).symm
      change LinearMap.toMatrix b b (ρ g) i i' = _
      rw [h1]
    · rintro ⟨g, hg, rfl⟩
      refine (hNmem g).2 ⟨fun v ↦ ?_, g.2⟩
      have h : ρ g = 1 := (LinearMap.toMatrix b b).injective (Matrix.ext hg)
      rw [h, Module.End.one_apply]
  -- its image `H` in `π₁(U₀)` is closed
  let H : Subgroup GU := N.map φ
  have hHc : IsClosed (H : Set GU) := by
    rw [Subgroup.coe_map, hNT, Set.image_image]
    exact (hT.isCompact.image ((continuous_fst.comp continuous_subtype_val).comp
      continuous_subtype_val)).isClosed
  -- it is normal, being normalised by the dense Weil group
  have hHn : H.Normal := by
    let S : Subgroup GU :=
      { carrier := {g | ∀ h ∈ H, g * h * g⁻¹ ∈ H ∧ g⁻¹ * h * g ∈ H}
        mul_mem' := fun {a b} ha hb h hh ↦
          ⟨by simpa [mul_assoc] using (ha _ (hb h hh).1).1,
            by simpa [mul_assoc] using (hb _ (ha h hh).2).2⟩
        one_mem' := fun h hh ↦ by simpa using hh
        inv_mem' := fun {a} ha h hh ↦ by simpa using (ha h hh).symm }
    have hSc : IsClosed (S : Set GU) := by
      have : (S : Set GU) =
          ⋂ h ∈ (H : Set GU), ({g | g * h * g⁻¹ ∈ H} ∩ {g | g⁻¹ * h * g ∈ H}) := by
        ext g
        simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact Iff.rfl
      rw [this]
      exact isClosed_biInter fun h _ ↦
        (hHc.preimage (by fun_prop)).inter (hHc.preimage (by fun_prop))
    have hN : N.Normal := inferInstance
    have hSW : ∀ w ∈ weilGroup pU sU GU, w.1 ∈ S := by
      intro w hw h hh
      obtain ⟨v, hv, rfl⟩ := hh
      exact ⟨⟨_, hN.conj_mem v hv ⟨w, hw⟩, rfl⟩, ⟨_, hN.conj_mem v hv ⟨w, hw⟩⁻¹, by simp [φ]⟩⟩
    have hS := eq_top_of_forall_mem_weilGroup pU GU S hSc hSW
    exact ⟨fun h hh g ↦ ((hS ▸ Subgroup.mem_top g : g ∈ S) h hh).1⟩
  -- it contains the inertia group, hence the local kernel
  have : Finite (C.residueField z.1) := boundary_subset_finitePoints (p := p) j z.2
  have hIH : (inertiaGroup sU GU (boundaryChart (p := p) j z)
      (boundaryChart (p := p) j z).point : Set GU) ⊆ H := by
    intro k hk
    have hkL := inertiaGroup_le_localKernel (p := p) sU GU _ _ hk
    have hkW : (k, (1 : Multiplicative ℤ)) ∈ weilGroup pU sU GU := by
      rw [mem_weilGroup_fundamentalGroupMap_iff j hj sU τ GU GC,
        MonoidHom.mem_ker.1 (localKernel_le_ker_restrictionMap j τ GU GC z.1 hkL)]
      exact (weilGroup p sC GC).one_mem
    refine ⟨⟨_, hkW⟩, (hNmem _).2 ⟨hI _ ⟨hk, rfl⟩, rfl⟩, rfl⟩
  have hle : localKernel (p := p) j sU GU z.1 ≤ H :=
    (localKernel_le_topologicalClosure_normalClosure (p := p) sU GU
      (boundaryChart (p := p) j z) z.2 _).trans
      (Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hIH) hHc)
  obtain ⟨hg, hdeg⟩ := hw
  obtain ⟨w', hw'N, hw'⟩ := hle hg
  obtain rfl : w' = w := Subtype.ext (Prod.ext hw' (((hNmem w').1 hw'N).2.trans hdeg.symm))
  exact ((hNmem w').1 hw'N).1 v

omit [Finite K] [IsCurve p] [GeometricallyConnected p] [ConnectedSpace C] [Smooth p]
  [IsOpenImmersion j] [Nonempty U] [IsIntegral C] [SmoothOfRelativeDimension 1 p] in
/-- An automorphism `σ` of a fibre functor acting trivially on the geometric fibres of all base
changes along `f` acts trivially on the geometric fibre of every object isomorphic to one. -/
lemma _root_.AlgebraicGeometry.Scheme.FiniteEtale.app_apply_eq_of_pullbackPathIso_eq_refl
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (f : X ⟶ Y)
    {y : Spec (.of Ω) ⟶ X} {σ : Aut (fiber y)} (hσ : pullbackPathIso f σ.asIso = Iso.refl _)
    {Q : X.FiniteEtale} {P : Y.FiniteEtale} (i : Q ≅ (pullback f).obj P) (a : (fiber y).obj Q) :
    σ.asIso.hom.app Q a = a := by
  have h₁ : σ.asIso.hom.app ((pullback f).obj P) = 𝟙 _ := by
    have h := congrArg (fun τ : fiber (y ≫ f) ≅ fiber (y ≫ f) ↦ τ.hom.app P) hσ
    simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app] at h
    rw [← cancel_epi ((pullbackFiberIso f y).inv.app P),
      ← cancel_mono ((pullbackFiberIso f y).hom.app P), Category.assoc, h]
    simp
  have h₂ : σ.asIso.hom.app Q = 𝟙 _ := by
    have h := σ.asIso.hom.naturality i.hom
    rw [h₁, Category.comp_id] at h
    rw [← cancel_mono ((fiber y).map i.hom), ← h, Category.id_comp]
  rw [h₂]
  rfl

omit [Nonempty U] in
/-- **Loops of `Ū` trivial on `V̄` push down into the kernel of `π₁(U₀) → π₁(V₀)`.** For a
morphism `k : U₀ ⟶ V₀` over `𝔽_q` and base point data `B` of the Weil group of `U₀`, a loop `σ`
of the geometric curve `Ū` at `B.t` acting trivially on the base changes of finite étale covers of
`V̄` maps to an element of `π₁(U₀, s_U)` acting trivially on the base changes of the finite étale
covers of `V₀`: these are base changes of covers of `V̄`, since `Ū ⟶ U₀ ⟶ V₀` is `Ū ⟶ V̄ ⟶ V₀`. -/
theorem BasePointData.geomAut_mem_fixingSubgroup
    (B : BasePointData (ofFundamentalGroup pU sU GU)) {V : Scheme.{u}} (k : U ⟶ V)
    {q : V ⟶ Spec (.of K)} (hk : k ≫ q = pU) {σ : Aut (fiber B.t)}
    (hσ : pullbackPathIso (Scheme.Hom.geometricFiberMap k hk) σ.asIso = Iso.refl _) :
    B.geomAut σ ∈ fixingSubgroup sU k GU := by
  intro P x
  set kb := Scheme.Hom.geometricFiberMap k hk
  have hsq : pU.geometricFiberProj ≫ k = kb ≫ q.geometricFiberProj :=
    (Scheme.Hom.geometricFiberMap_comp_geometricFiberProj k hk).symm
  -- the loop pushed down to `U₀` acts trivially on the fibres of `k^* P`
  let e := pullbackPathIso pU.geometricFiberProj σ.asIso ≪≫ eqToIso (congrArg fiber
    (rfl : B.t ≫ pU.geometricFiberProj = B.t ≫ pU.geometricFiberProj))
  have he (a) : e.hom.app ((pullback k).obj P) a = a := by
    simp only [e, eqToIso_refl, Iso.trans_refl, pullbackPathIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      ConcreteCategory.comp_apply]
    erw [app_apply_eq_of_pullbackPathIso_eq_refl kb hσ
      ((pullbackCompIso _ _ _).symm ≪≫ eqToIso (congrArg (fun m ↦ (pullback m).obj P) hsq) ≪≫
        pullbackCompIso _ _ _)]
    exact ConcreteCategory.congr_hom
      ((pullbackFiberIso pU.geometricFiberProj B.t).inv_hom_id_app _) a
  have key := B.toAutMulEquiv_toπ (Aut.of e)
  change (show GU from B.toπ (Aut.of e)) • x = x
  rw [← toAut_hom_app_apply, ← toAutMulEquiv_apply]
  erw [key]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [he]
  exact ConcreteCategory.congr_hom (B.path.inv_hom_id_app _) x

end AlgebraicGeometry.WeilGroup

namespace AlgebraicGeometry.WeilSheaf

open WeilGroup Scheme.FiniteEtale ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The pullback of a Weil sheaf along the identity is the sheaf itself: both `𝟙^*` and the
identity functor are left adjoint to `𝟙_* ≅ 𝟭`. -/
theorem nonempty_upperStar_id_iso {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X) :
    Nonempty ((upperStar (𝟙 X)).obj F ≅ F) :=
  ⟨((WeilSheaf.upperStarLowerStarAdjunction (k₀ := k₀) (l := l) (𝟙 X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (lowerStarIdIso k₀ l X).symm)).app F⟩

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale ProEtale WeilSheaf

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} [C.Over (Spec (.of K))]
  [U.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [IsIntegral C] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [Smooth (C ↘ Spec (.of K))]
  [IsCurve (U ↘ Spec (.of K))] [GeometricallyConnected (U ↘ Spec (.of K))] [ConnectedSpace U]
  (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [Nonempty U] [j.IsOver (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

omit [Finite K] [GeometricallyConnected (C ↘ Spec (.of K))] [IsIntegral C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))] [IsCurve (U ↘ Spec (.of K))]
  [GeometricallyConnected (U ↘ Spec (.of K))] [ConnectedSpace U] [QuasiCompact j] in
/-- The open immersion `U₀ ⟶ U₀ ∪ {z}` is a morphism over `𝔽_q`. -/
lemma toBoundaryOpen_comp_over (z : C) :
    toBoundaryOpen (p := C ↘ Spec (.of K)) j z ≫
      ((boundaryOpen (p := C ↘ Spec (.of K)) j z).ι ≫ C ↘ Spec (.of K)) = U ↘ Spec (.of K) := by
  rw [← Category.assoc, toBoundaryOpen_eq, IsOpenImmersion.lift_fac]
  exact comp_over j _

omit [IsIntegral C] [GeometricallyConnected (U ↘ Spec (.of K))] [ConnectedSpace U] in
/-- **Purity at a boundary point with trivial local monodromy.** Let `j : U₀ ⟶ C₀` be a nonempty
open of a smooth geometrically connected curve, `z` a boundary point, `V₀ = U₀ ∪ {z}` and `F` a
lisse Weil sheaf on `U₀`, punctually `ι`-pure of weight `w`. If the monodromy of `F` on `Ū` at a
geometric point `t` (`AlgebraicGeometry.ProEtale.universalLisseMonodromy`) is trivial on the
kernel of `π₁(Ū, t) → π₁(V̄, t)`, then the stalk `(j_* F)_z̄` is `ι`-pure of weight `w`: `F`
extends to a lisse Weil sheaf `G` on `V₀`
(`AlgebraicGeometry.WeilSheaf.exists_isLisse_upperStar_iso_of_rep_eq_self`), which is pure of
weight `w` since its restriction to `U₀` is
(`AlgebraicGeometry.WeilSheaf.IsLisse.isPunctuallyPureOfWeight_of_upperStar`), and
`(j_* F)_z̄ = ((U₀ ⟶ V₀)_* F)_z̄ = G_z̄` (`lemma-boundary-stalk--2`).
(blueprint: `corollary-unramified-boundary-point--2`) -/
theorem isPureOfWeight_stalk_directImage_of_rep_eq_self (z : ↥((Set.range j.base)ᶜ))
    {F : WeilSheaf K l U} (hF : F.IsLisse)
    (t : Spec (.of (AlgebraicClosure K)) ⟶ (U ↘ Spec (.of K)).geometricFiber)
    [IsRegular (U ↘ Spec (.of K)).geometricFiber]
    [ConnectedSpace (U ↘ Spec (.of K)).geometricFiber]
    (hFt : ∀ σ : Aut (fiber t), pullbackPathIso (Scheme.Hom.geometricFiberMap
        (toBoundaryOpen (p := C ↘ Spec (.of K)) j z.1)
        (g := (boundaryOpen (p := C ↘ Spec (.of K)) j z.1).ι ≫ C ↘ Spec (.of K))
        (toBoundaryOpen_comp_over j z.1)) σ.asIso = Iso.refl _ →
      ∀ v, (universalLisseMonodromy l (U ↘ Spec (.of K)).geometricFiber K).rep t
        ⟨F.obj.carrier, hF⟩ σ v = v)
    {ι : PadicAlgCl l →+* ℂ} {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w)
    (x : C.finitePoints) (hx : x.1 = z.1) :
    (((directImage j).obj F).stalk x).IsPureOfWeight ι
      ((C ↘ Spec (.of K)).residueCard x.1) w := by
  classical
  set p := C ↘ Spec (.of K)
  set V := boundaryOpen (p := p) j z.1
  let : V.toScheme.Over (Spec (.of K)) := ⟨V.ι ≫ p⟩
  set k := toBoundaryOpen (p := p) j z.1
  have hkV : k ≫ V.toScheme ↘ Spec (.of K) = U ↘ Spec (.of K) := toBoundaryOpen_comp_over j z.1
  have hkι : k ≫ V.ι = j := by
    simp only [k, toBoundaryOpen_eq]
    exact IsOpenImmersion.lift_fac _ _ _
  have : k.IsOver (Spec (.of K)) := ⟨hkV⟩
  have : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (toComplOpens _ _ _ _ _))
  have : V.ι.IsOver (Spec (.of K)) := ⟨rfl⟩
  -- `V₀ = U₀ ∪ {z}` is a smooth geometrically connected curve
  have : SmoothOfRelativeDimension 1 (V.toScheme ↘ Spec (.of K)) :=
    (zero_add 1) ▸ (inferInstance : SmoothOfRelativeDimension (0 + 1) (V.ι ≫ p))
  have : Smooth (V.toScheme ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ p))
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  have : CompactSpace V.toScheme := ProEtale.compactSpace_of_isOpenImmersion V.ι
  have : QuasiCompact (V.toScheme ↘ Spec (.of K)) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have : QuasiSeparated (V.toScheme ↘ Spec (.of K)) :=
    inferInstanceAs (QuasiSeparated (V.ι ≫ p))
  have : Nonempty V.toScheme := ⟨k.base (Nonempty.some inferInstance)⟩
  have : GeometricallyConnected (V.toScheme ↘ Spec (.of K)) := by
    have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected p
    have := GeometricallyIrreducible.comp_of_isOpenImmersion V.ι p
    exact inferInstanceAs (GeometricallyConnected (V.ι ≫ p))
  have : QuasiCompact k := by
    have : QuasiCompact (k ≫ V.toScheme ↘ Spec (.of K)) := by rw [hkV]; infer_instance
    exact QuasiCompact.of_comp k (V.toScheme ↘ Spec (.of K))
  -- `U₀` is dense in the irreducible `V₀`
  have : IrreducibleSpace C := irreducibleSpace_of_smooth (p := p)
  have : IrreducibleSpace V.toScheme := by
    obtain ⟨c⟩ := (inferInstance : Nonempty V.toScheme)
    have hirr : IsIrreducible (V : Set C) :=
      ⟨⟨_, c.2⟩, (IrreducibleSpace.isIrreducible_univ C).isPreirreducible.open_subset V.isOpen
        (Set.subset_univ _)⟩
    exact Subtype.irreducibleSpace hirr
  have hkd : Dense (Set.range k.base) :=
    k.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  have : IsDominant k := ⟨hkd⟩
  -- the geometric curve `Ū`
  have : Smooth (U ↘ Spec (.of K)) := by rw [← comp_over j (Spec (.of K))]; infer_instance
  -- `F` extends to a lisse Weil sheaf `G` on `V₀`
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_isLisse_upperStar_iso_of_rep_eq_self k hkd hF t
    fun σ hσ v ↦ hFt σ (congrArg Aut.asIso (MonoidHom.mem_ker.1 hσ)) v
  -- `G` is pure of weight `w`
  have hres : ((upperStar k).obj G).IsPunctuallyPureOfWeight ι w := fun y ↦
    (hw y).of_equiv (nonempty_equiv_stalk_of_iso e y).some
  have hGw := hG.isPunctuallyPureOfWeight_of_upperStar k hres
  -- the stalk of `j_* F` at `z` is that of `G`
  have hzV : z.1 ∈ V := (mem_boundaryOpen_iff j).2 (Or.inr rfl)
  have hy : (⟨z.1, hzV⟩ : V.toScheme) ∈ V.toScheme.finitePoints := by
    rw [← Scheme.Hom.mem_finitePoints_iff_of_isIso V.ι]
    have hzf : z.1 ∈ C.finitePoints := hx ▸ x.2
    exact hzf
  let y : V.toScheme.finitePoints := ⟨_, hy⟩
  have hyx : V.ι.base y.1 = x.1 := hx.symm
  have hsq : IsPullback k (𝟙 U) V.ι j := IsPullback.of_vert_isIso_mono ⟨by rw [hkι]; simp⟩
  obtain ⟨E₁⟩ := nonempty_equiv_stalk_directImage_of_isPullback hsq F y x hyx
  obtain ⟨i₁⟩ := nonempty_upperStar_id_iso F
  obtain ⟨i₂⟩ := hG.nonempty_iso_directImage_upperStar k hkd
  obtain ⟨E₂⟩ := nonempty_equiv_stalk_of_iso
    ((directImage k).mapIso (i₁ ≪≫ e.symm) ≪≫ i₂.symm) y
  have hdeg : (V.toScheme ↘ Spec (.of K)).residueCard y.1 = p.residueCard x.1 := by
    rw [Scheme.Hom.residueCard, Scheme.Hom.residueCard, ← hyx,
      ← Scheme.Hom.degreeOver_comp_of_isIso V.ι p y.1]
    rfl
  have h := hGw y
  rw [hdeg] at h
  exact h.of_equiv (E₁.trans E₂)

variable (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

/-- Blueprint `corollary-unramified-boundary-point--2` (first clause, inertia form), together with
`definition-weil-representation--1`.

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over `𝔽_q`, `U₀`
geometrically connected, with the boundary datum of actual inertia groups and residue Frobenius
lifts (`AlgebraicGeometry.WeilGroup.boundaryDatum`). There is a lisse sheaf–representation
equivalence `ℱ ↦ (V, ρ)` for `W(U₀)`, identifying the stalk `ℱ_x̄` with its local Frobenius with
`V` with `ρ (Frob_x)` at the closed points of `U₀`, such that: if `ℱ` is punctually `ι`-pure of
weight `w` and the inertia group `I_z` at a boundary point `z` acts trivially on `V` (the boundary
stalk `V ^ (I_z)` is everything), then the stalk `(j_* ℱ)_z̄` is `ι`-pure of weight `w`.

The equivalence is the Weil fundamental representation at the monodromy of universal covers
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_of_lisseMonodromy`). A representation
trivial on `I_z` is trivial on the kernel of `π₁(U₀) → π₁(U₀ ∪ {z})`
(`AlgebraicGeometry.WeilGroup.apply_eq_self_of_mem_weilLocalKernel`), which contains the images
of the loops of `Ū` trivial on `V̄`
(`AlgebraicGeometry.WeilGroup.BasePointData.geomAut_mem_fixingSubgroup`); so `ℱ` extends to a
lisse Weil sheaf on `U₀ ∪ {z}` and the stalk is pure
(`AlgebraicGeometry.WeilGroup.isPureOfWeight_stalk_directImage_of_rep_eq_self`). -/
theorem exists_equivalence_isLisse_isPureOfWeight_stalk_directImage :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
          (x : U.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ
            ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).frobenius x) (f v)) ∧
      ∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
        (z : ↥((Set.range j.base)ᶜ)),
        (boundaryDatum (p := C ↘ Spec (.of K)) j sU GU (comp_over j _) τ GC).boundaryStalk l
            (e.functor.obj F).obj.ρ z = ⊤ →
        ∀ {ι : PadicAlgCl l →+* ℂ} {w : ℝ}, F.obj.IsPunctuallyPureOfWeight ι w →
          ∀ x : C.finitePoints, x.1 = z.1 →
            (((directImage j).obj F.obj).stalk x).IsPureOfWeight ι
              ((C ↘ Spec (.of K)).residueCard x.1) w := by
  have hjU : j ≫ C ↘ Spec (.of K) = U ↘ Spec (.of K) := comp_over j _
  have : SmoothOfRelativeDimension 1 (U ↘ Spec (.of K)) :=
    hjU ▸ (zero_add 1) ▸ (inferInstance : SmoothOfRelativeDimension (0 + 1) (j ≫ C ↘ Spec (.of K)))
  have : Smooth (U ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have : ConnectedSpace (U ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := U ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (U ↘ Spec (.of K)).geometricFiberProj
      (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Smooth (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  set W := ofFundamentalGroup (U ↘ Spec (.of K)) sU GU
  obtain ⟨B⟩ := nonempty_basePointData W
  set M := universalLisseMonodromy l (U ↘ Spec (.of K)).geometricFiber K
  obtain ⟨e, h₁, -, -, -, hf⟩ := exists_equivalence_isLisse_of_lisseMonodromy W l M B
    (universalLisseMonodromy_isEquivalenceAt l _ K B.t)
  refine ⟨e, h₁, fun F z hz ι w hw x hx ↦ ?_⟩
  obtain ⟨f, hf⟩ := hf F
  -- inertia acts trivially
  have hI : ∀ g ∈ boundaryInertia (p := C ↘ Spec (.of K)) (pU := U ↘ Spec (.of K)) j sU GU z,
      ∀ v, (e.functor.obj F).obj.ρ g v = v := fun g hg v ↦ by
    have hv : v ∈ (boundaryDatum (p := C ↘ Spec (.of K)) j sU GU hjU τ GC).boundaryStalk l
        (e.functor.obj F).obj.ρ z := hz ▸ Submodule.mem_top
    exact (Representation.mem_invariants _ v).1 hv ⟨g, hg⟩
  refine isPureOfWeight_stalk_directImage_of_rep_eq_self j z F.property B.t
    (fun σ hσ v ↦ ?_) hw x hx
  -- the loop `σ` lies in the local kernel at `z`
  have hmem : (B.geomEquiv σ : W.carrier) ∈
      weilLocalKernel (p := C ↘ Spec (.of K)) (pU := U ↘ Spec (.of K)) j sU GU z.1 := by
    refine ⟨?_, (B.geomEquiv σ).2⟩
    have h : B.geomAut σ ∈ fixingSubgroup sU (toBoundaryOpen (p := C ↘ Spec (.of K)) j z.1) GU :=
      BasePointData.geomAut_mem_fixingSubgroup sU GU B _ (toBoundaryOpen_comp_over j z.1) hσ
    have hg := B.weilGroupEquiv_geomHom σ
    refine Subgroup.mem_comap.2 ?_
    have h' : ((MonoidHom.fst _ _).comp (weilGroup (U ↘ Spec (.of K)) sU GU).subtype)
        (B.geomEquiv σ : W.carrier) = B.geomAut σ := congrArg Prod.fst hg
    rw [h']
    exact h
  have := (e.functor.obj F).property.1
  have hρ := apply_eq_self_of_mem_weilLocalKernel j hjU sU GU τ GC l
    (e.functor.obj F).property.2 z hI hmem
  have key := hf (B.geomEquiv σ) (f.symm v)
  erw [hρ (f.symm v)] at key
  rw [LinearEquiv.apply_symm_apply, fundamentalRep_geometric] at key
  erw [ContinuousMulEquiv.symm_apply_apply] at key
  exact key.symm

end AlgebraicGeometry.WeilGroup
