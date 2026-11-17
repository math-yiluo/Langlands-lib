import Langlands.GroupScheme.Torus.MaximalFibreSpreadingStatement
import Langlands.GroupScheme.Torus.RelativeCentralizerDescent
import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothProof
import Langlands.GroupScheme.SmoothMonoLocalIso
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Torus.MaximalFibreSpreadingBaseChange

/-! # Spreading maximality from a fibre with reductive identity component -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.MaximalFibreSpreading

/-- A map from a geometrically connected group lifts to a represented relative
identity component. -/
def liftToComponent {S : Scheme.{u}} {C H P : GroupScheme S}
    (e : H ⟶ C) (he : IsRelativeIdentityComponent C e)
    [GeometricallyConnected P.X.hom] (f : P ⟶ C) : P ⟶ H := by
  let : IsOpenImmersion e.hom.hom.left := he.isOpenImmersion
  apply IdentityComponent.liftHom e f
  rw [he.range_eq_underlyingSet]
  apply (RelativeIdentityComponent.inRelativeIdentityComponent_iff_range_subset C _).mp
  exact RelativeIdentityComponent.inRelativeIdentityComponent_of_geometricallyConnected
    C f.hom.hom η[P.X] (IsMonHom.one_hom _)

@[reassoc (attr := simp)]
theorem liftToComponent_comp {S : Scheme.{u}} {C H P : GroupScheme S}
    (e : H ⟶ C) (he : IsRelativeIdentityComponent C e)
    [GeometricallyConnected P.X.hom] (f : P ⟶ C) :
    liftToComponent e he f ≫ e = f := by
  let : IsOpenImmersion e.hom.hom.left := he.isOpenImmersion
  exact IdentityComponent.liftHom_fac _ _ _

/-- A connected subgroup of a torus centralizer containing a maximal torus
is that torus when the ambient identity component is reductive. -/
theorem isIso_of_connected_centralizing
    {k : Type u} [Field k]
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace C.X.left]
    (hG : IsConnectedReductive (identityComponent G))
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (c : C ⟶ G) [Mono c.hom.hom]
    (hZ : SubgroupFunctor.range c ≤ torusCentralizer i)
    (f : T.toGrp ⟶ C) (hf : f ≫ c = i) : IsIso f := by
  let : ConnectedSpace T.X.left := hi.1.connectedSpace
  let i₀ := IdentityComponent.factor G i
  let c₀ := IdentityComponent.factor G c
  have hi₀ : IsMaximalTorus i₀ := by
    apply IsMaximalTorus.of_comp (IdentityComponent.isClosedSubgroup_identityComponentι G)
    simpa only [i₀, IdentityComponent.factor_identityComponentι] using hi
  have hself := maximalTorusCentralizer k (identityComponent G) hG T i₀ hi₀
  have hle : SubgroupFunctor.range c₀ ≤ SubgroupFunctor.range i₀ := by
    rw [← hself]
    intro U x hx V a t
    rw [SubgroupFunctor.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    apply (commute_iff_eq _ _).mpr
    apply (cancel_mono (identityComponentι G).hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    have hc := hZ U (show y ≫ c.hom.hom ∈ (SubgroupFunctor.range c).carrier U
      from ⟨y, rfl⟩) V a t
    simpa only [Category.assoc, ← Grp.comp_hom_hom, i₀, c₀,
      IdentityComponent.factor_identityComponentι] using hc.eq
  let : IsClosedImmersion i₀.hom.hom.left := hi₀.2.1
  have hiRep : (SubgroupFunctor.range i₀).IsRepresentedBy i₀ :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let g := hiRep.factorHom c₀ hle
  have hg : g ≫ i = c := by
    rw [← IdentityComponent.factor_identityComponentι G i, ← Category.assoc,
      hiRep.factorHom_comp]
    exact IdentityComponent.factor_identityComponentι G c
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  have hiRep' : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hcRep : (SubgroupFunctor.range c).IsRepresentedBy c := ⟨inferInstance, rfl⟩
  let e : T.toGrp ≅ C :=
    { hom := f
      inv := g
      hom_inv_id := hiRep'.hom_ext (by simp only [Category.assoc, hg, hf, Category.id_comp])
      inv_hom_id := hcRep.hom_ext (by simp only [Category.assoc, hf, hg, Category.id_comp]) }
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- A geometrically connected open and closed subgroup represents the relative
identity component. -/
theorem component_of_open_closed {S : Scheme.{u}} {C P : GroupScheme S}
    (j : P ⟶ C) [GeometricallyConnected P.X.hom]
    [IsOpenImmersion j.hom.hom.left] [IsClosedImmersion j.hom.hom.left] :
    IsRelativeIdentityComponent C j := by
  apply IsRelativeIdentityComponent.of_range_residueFiber
  intro s
  let b := S.fromSpecResidueField s
  let : ConnectedSpace ((baseChange b).obj P).X.left :=
    inferInstanceAs (ConnectedSpace (P.X.hom.fiber s))
  let : IsOpenImmersion ((baseChange b).map j).hom.hom.left :=
    MorphismProperty.of_isPullback
      (RelativeIdentityComponent.overPullback_isPullback b j.hom.hom).flip inferInstance
  let : IsClosedImmersion ((baseChange b).map j).hom.hom.left :=
    MorphismProperty.of_isPullback
      (RelativeIdentityComponent.overPullback_isPullback b j.hom.hom).flip inferInstance
  exact IdentityComponent.range_eq_identitySet ((baseChange b).obj C) ((baseChange b).map j)

/-- A torus that represents the relative identity component of its centralizer
is maximal, without a reductivity assumption. -/
theorem isMaximalTorus_of_component
    {k : Type u} [Field k]
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (c : C ⟶ G) (hc : (torusCentralizer i).IsRepresentedBy c)
    (j : T.toGrp ⟶ C) (hj : IsRelativeIdentityComponent C j) (hji : j ≫ c = i) :
    IsMaximalTorus i := by
  refine ⟨hT, hi, ?_⟩
  intro T' i' f hT' hi' hf
  let g := hc.factorHom i' (range_le_torusCentralizer_of_factor i i' f hf)
  have hg : g ≫ c = i' := hc.factorHom_comp _ _
  let : GeometricallyConnected T'.X.hom := hT'.isRelativeTorus.geometricallyConnected
  let r := liftToComponent j hj g
  have hr : r ≫ i = i' := by
    rw [← hji, ← Category.assoc, liftToComponent_comp]
    exact hg
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion i'.hom.hom.left := hi'
  have hiRep : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hiRep' : (SubgroupFunctor.range i').IsRepresentedBy i' :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact ⟨⟨r, hiRep.hom_ext (by simp only [Category.assoc, hr, hf, Category.id_comp]),
    hiRep'.hom_ext (by simp only [Category.assoc, hf, hr, Category.id_comp])⟩⟩

/-- The group-scheme forgetful functor detects isomorphisms of underlying schemes. -/
theorem isIso_of_underlying {S : Scheme.{u}} {P H : GroupScheme S} (f : P ⟶ H)
    [IsIso f.hom.hom.left] : IsIso f := by
  have : IsIso ((Over.forget S).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget S)
  exact (Grp.mkIso' (asIso f.hom.hom)).isIso_hom

/-- The comparison with the connected centralizer is an isomorphism on the
specified geometric fibre. -/
theorem isIso_geometric_comparison
    {S : Scheme.{u}} {G C H : GroupScheme S} {T : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [GeometricallyConnected H.X.hom]
    (i : T.toGrp ⟶ G) (c : C ⟶ G)
    (hc : (torusCentralizer i).IsRepresentedBy c) (hcc : IsClosedSubgroup c)
    (e : H ⟶ C) (he : IsRelativeIdentityComponent C e)
    (f : T.toGrp ⟶ H) (hf : f ≫ (e ≫ c) = i)
    (s : S) (hs : s ∈ identityComponentReductiveLocus G)
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
      ((baseChange (S.fromSpecResidueField s)).map i)) :
    IsIso ((baseChange (geometricPoint S s)).map f) := by
  let b := geometricPoint S s
  let B := baseChange b
  let : IsClosedImmersion c.hom.hom.left := hcc
  let : IsOpenImmersion e.hom.hom.left := he.isOpenImmersion
  let : Mono e.hom.hom := Over.mono_of_mono_left _
  let : Mono c.hom.hom := hc.1
  let : Mono (e ≫ c).hom.hom := by
    change Mono (e.hom.hom ≫ c.hom.hom)
    infer_instance
  let : Mono (B.map (e ≫ c)).hom.hom := by
    change Mono ((Over.pullback b).map (e ≫ c).hom.hom)
    infer_instance
  let : Smooth (B.obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom (B.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  let : GeometricallyConnected (B.obj H).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.X.hom b))
  let : ConnectedSpace (B.obj H).X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (B.obj H).X.hom
  have hb : b (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) = s := by
    exact Scheme.fromSpecResidueField_apply s _
  have hmaxb := isMaximalTorus_fieldPoint_of_residueFibre b (by rwa [hb])
  have hcb : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T) (B.map i)).IsRepresentedBy (B.map c) := by
    rw [torusCentralizer_baseChange]
    exact hc.baseChange b
  have hZ : SubgroupFunctor.range (B.map (e ≫ c)) ≤ torusCentralizer (T := (CommGroupScheme.baseChange b).obj T) (B.map i) := by
    rw [← hcb.2]
    intro U x hx
    rw [SubgroupFunctor.mem_range] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    refine ⟨y ≫ (B.map e).hom.hom, ?_⟩
    simp only [Category.assoc, ← Grp.comp_hom_hom, ← Functor.map_comp]
  exact isIso_of_connected_centralizing (T := (CommGroupScheme.baseChange b).obj T) hs (B.map i) hmaxb
    (B.map (e ≫ c)) hZ (B.map f) (by rw [← B.map_comp, hf])

/-- Isomorphisms of iterated pullbacks transfer to pullback along the composite. -/
theorem isIso_baseChange_comp {S S' S'' : Scheme.{u}}
    (a : S' ⟶ S) (b : S'' ⟶ S') {P H : GroupScheme S} (f : P ⟶ H)
    [IsIso ((baseChange b).map ((baseChange a).map f))] :
    IsIso ((baseChange (b ≫ a)).map f) := by
  have hnat := baseChangeCompIso_hom_naturality a b f
  have heq : (baseChange (b ≫ a)).map f =
      (baseChangeCompIso a b P).hom ≫ (baseChange b).map ((baseChange a).map f) ≫
        (baseChangeCompIso a b H).inv := by
    rw [← reassoc_of% hnat, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

/-- An isomorphism over an open induces an isomorphism over each original residue
field of a point in that open. -/
theorem isIso_residueFibre_of_restriction {S : Scheme.{u}} {P H : GroupScheme S}
    (f : P ⟶ H) (V : S.Opens) [IsIso ((baseChange V.ι).map f)]
    (v : S) (hv : v ∈ V) :
    IsIso ((baseChange (S.fromSpecResidueField v)).map f) := by
  let b := S.fromSpecResidueField v
  let l : Spec (S.residueField v) ⟶ V := IsOpenImmersion.lift V.ι b (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change S.fromSpecResidueField v z ∈ V
    rw [Scheme.fromSpecResidueField_apply]
    exact hv)
  have hl : l ≫ V.ι = b := IsOpenImmersion.lift_fac _ _ _
  have h : IsIso ((baseChange (l ≫ V.ι)).map f) := isIso_baseChange_comp V.ι l f
  rw [hl] at h
  exact h

end Langlands.GroupScheme.MaximalFibreSpreading

namespace Langlands.GroupScheme

open MaximalFibreSpreading

/-- Maximality on a fibre with reductive identity component spreads to an open
neighbourhood, where the torus is the relative identity component of its centralizer. -/
theorem maximalTorusFibreSpreading : MaximalTorusFibreSpreadingStatement.{u} := by
  intro S G _ _ T i hT hi s hs hmax
  obtain ⟨C, c, hcc, hCs, hc⟩ :=
    relativeTorusCentralizer_hasSmoothClosedRepresentative i hT inferInstance
  obtain ⟨H, e, he, hHs, hHgc⟩ := RelativeIdentityComponent.smoothStructure.1 S C hCs
  let : Smooth T.X.hom := hT.smooth
  let : GeometricallyConnected T.X.hom := hT.geometricallyConnected
  let : Smooth H.X.hom := hHs
  let : GeometricallyConnected H.X.hom := hHgc
  let a := torusCentralizerFactor i hc
  have hac : a ≫ c = i := torusCentralizerFactor_comp i hc
  have haclosed : IsClosedSubgroup a := isClosedSubgroup_torusCentralizerFactor i hc hcc hi
  let f := liftToComponent e he a
  have hfe : f ≫ e = a := liftToComponent_comp e he a
  have hf : f ≫ (e ≫ c) = i := by rw [← Category.assoc, hfe, hac]
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono f.hom.hom.left :=
    mono_of_mono_fac (congrArg (fun g => g.hom.hom.left) hf)
  have hfgeo : IsIso ((baseChange (geometricPoint S s)).map f) :=
    isIso_geometric_comparison i c hc hcc e he f hf s hs hmax
  let : IsIso ((baseChange (S.fromSpecResidueField s)).map f) :=
    isIso_residueFibre_of_isIso_geometricFibre f s hfgeo
  have hfres : IsIso (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left) :=
    inferInstanceAs (IsIso (((Grp.forget _).comp (Over.forget _)).map
      ((baseChange (S.fromSpecResidueField s)).map f)))
  obtain ⟨V, hVs, hVf⟩ := SmoothMonoLocalIso.isIsoNear_of_residueFiber f s hfres
  let : IsIso (((baseChange V.ι).map f).hom.hom.left) := hVf
  let : IsIso ((baseChange V.ι).map f) := isIso_of_underlying _
  have haVopen : IsOpenImmersion (((baseChange V.ι).map a).hom.hom.left) := by
    let : IsOpenImmersion (((baseChange V.ι).map e).hom.hom.left) :=
      (he.baseChange V.ι).isOpenImmersion
    rw [← hfe, Functor.map_comp]
    change IsOpenImmersion
      (((baseChange V.ι).map f).hom.hom.left ≫ ((baseChange V.ι).map e).hom.hom.left)
    infer_instance
  refine ⟨V, hVs, ?_, ?_⟩
  · intro v hv
    let b := S.fromSpecResidueField v
    let B := baseChange b
    let : IsIso (B.map f) := isIso_residueFibre_of_restriction f V v hv
    let : IsOpenImmersion (B.map e).hom.hom.left := (he.baseChange b).isOpenImmersion
    let : IsOpenImmersion (B.map a).hom.hom.left := by
      rw [← hfe, B.map_comp]
      change IsOpenImmersion ((B.map f).hom.hom.left ≫ (B.map e).hom.hom.left)
      infer_instance
    let : IsClosedImmersion (B.map a).hom.hom.left := haclosed.baseChange b
    let : GeometricallyConnected (B.obj T.toGrp).X.hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd T.X.hom b))
    have hcb : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
        (B.map i)).IsRepresentedBy (B.map c) := by
      rw [torusCentralizer_baseChange]
      exact hc.baseChange b
    exact isMaximalTorus_of_component (T := (CommGroupScheme.baseChange b).obj T)
      (B.map i) (hT.baseChange b).isTorus (hi.baseChange b) (B.map c) hcb (B.map a)
      (component_of_open_closed (B.map a)) (by rw [← B.map_comp, hac])
  · intro Z z j hz hj
    let d : C ≅ Z := hc.isoOfIsRepresentedBy hz
    have hd : d.hom ≫ z = c := hc.isoOfIsRepresentedBy_hom_comp hz
    have haj : a ≫ d.hom = j := hz.hom_ext (by rw [Category.assoc, hd, hac, hj])
    let : GeometricallyConnected ((baseChange V.ι).obj T.toGrp).X.hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd T.X.hom V.ι))
    let : IsOpenImmersion (((baseChange V.ι).map a).hom.hom.left) := haVopen
    let : IsClosedImmersion (((baseChange V.ι).map a).hom.hom.left) := haclosed.baseChange V.ι
    let : IsOpenImmersion (((baseChange V.ι).map j).hom.hom.left) := by
      rw [← haj, Functor.map_comp]
      change IsOpenImmersion
        (((baseChange V.ι).map a).hom.hom.left ≫ ((baseChange V.ι).map d.hom).hom.hom.left)
      infer_instance
    let : IsClosedImmersion (((baseChange V.ι).map j).hom.hom.left) := by
      rw [← haj, Functor.map_comp]
      change IsClosedImmersion
        (((baseChange V.ι).map a).hom.hom.left ≫ ((baseChange V.ι).map d.hom).hom.hom.left)
      infer_instance
    exact component_of_open_closed ((baseChange V.ι).map j)

end Langlands.GroupScheme
