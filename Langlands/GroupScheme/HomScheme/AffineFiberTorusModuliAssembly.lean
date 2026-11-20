import Langlands.GroupScheme.HomScheme.AdmissibleBaseChange
import Langlands.GroupScheme.HomScheme.AffineFiberTorusConnectedReduction
import Langlands.GroupScheme.HomScheme.FixedCentralizerTorusModuli

/-! # Smooth torus moduli from adic effectivity and a smooth centralizer parameter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor Langlands.AlgebraicGeometry.UnramifiedFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- The smooth ambient centralizer parameter and the all-test property
needed to recover the base point of any actual closed torus. -/
structure SmoothTorusCentralizerParameter (G : GroupScheme S) where
  base : Over S
  group : GroupScheme base.left
  inclusion : group ⟶ (baseChange base.hom).obj G
  closed : IsClosedSubgroup inclusion
  smooth_base : Smooth base.hom
  smooth_group : Smooth group.X.hom
  connected_group : GeometricallyConnected group.X.hom
  universal : ∀ (U : Over S) (F : SubgroupFunctor ((baseChange U.hom).obj G)),
    IsAdmissible F → ∃! a : U ⟶ base, evaluate inclusion a = F.centralizer

private theorem comap_iso_injective {B : Scheme.{u}} {P Q : GroupScheme B} (e : P ≅ Q) :
    Function.Injective (SubgroupFunctor.comap e.hom) := by
  intro F F' h
  have he := congrArg (SubgroupFunctor.comap e.inv) h
  simpa only [← comap_comp, Iso.inv_hom_id, comap_id] using he

private theorem centralizer_comap_iso {B : Scheme.{u}} {P Q : GroupScheme B} (e : P ≅ Q)
    (F : SubgroupFunctor Q) (hF : IsAdmissible F) :
    (F.comap e.hom).centralizer = F.centralizer.comap e.hom := by
  let r := admissibleRepresentative ⟨F, hF⟩
  have h := centralizer_range_eq_comap_of_iso (r.hom ≫ e.inv) e
  have hleft : range (r.hom ≫ e.inv) = comap e.hom (range r.hom) :=
    range_comp_iso r.hom e.symm
  rw [hleft, Category.assoc, Iso.inv_hom_id, Category.comp_id, r.represents.2] at h
  exact h

variable {M U : Over S} {N : Over M.left} {L : GroupScheme N.left}

private def overParameter (p : U ⟶ M) (a : Over.mk p.left ⟶ N) :
    U ⟶ (Over.map M.hom).obj N :=
  Over.homMk a.left (by
    change a.left ≫ (N.hom ≫ M.hom) = U.hom
    rw [← Category.assoc, a.w]
    exact p.w)

set_option maxHeartbeats 1200000 in
private theorem familyHom_overParameter (p : U ⟶ M) (a : Over.mk p.left ⟶ N)
    (l : L ⟶ (baseChange N.hom).obj ((baseChange M.hom).obj G)) :
    familyHom (pushFamily M.hom l) (overParameter p a) =
      familyHom l a ≫ (Descent.pullbackComparison M.hom p.left U.hom p.w G).hom := by
  let e := Descent.pullbackComparison M.hom p.left U.hom p.w G
  let k : (baseChange a.left).obj L ⟶ (baseChange U.hom).obj G :=
    familyHom (pushFamily M.hom l) (overParameter p a)
  let k' : (baseChange a.left).obj L ⟶ (baseChange U.hom).obj G := familyHom l a ≫ e.hom
  have h₁ := familyHom_original (S := S) (G := G) (M := (Over.map M.hom).obj N)
    (T := U) (K := L) (pushFamily M.hom l) (overParameter p a)
  have h₂ := familyHom_original_assoc (S := M.left) (G := (baseChange M.hom).obj G)
    (M := N) (T := Over.mk p.left) (K := L) l a (pullback.fst G.X.hom M.hom)
  change k = k'
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (familyHom (pushFamily M.hom l) (overParameter p a)).hom.hom.left ≫
        pullback.fst G.X.hom U.hom =
      (familyHom l a).hom.hom.left ≫ e.hom.hom.hom.left ≫ pullback.fst G.X.hom U.hom
    calc
      _ = pullback.fst L.X.hom a.left ≫ (pushFamily M.hom l).hom.hom.left ≫
          pullback.fst G.X.hom (N.hom ≫ M.hom) := h₁
      _ = pullback.fst L.X.hom a.left ≫ l.hom.hom.left ≫
          pullback.fst ((baseChange M.hom).obj G).X.hom N.hom ≫ pullback.fst G.X.hom M.hom := by
        simp only [pushFamily, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
          Descent.pullbackComparison_hom_fst]
      _ = (familyHom l a).hom.hom.left ≫
          pullback.fst ((baseChange M.hom).obj G).X.hom p.left ≫
          pullback.fst G.X.hom M.hom := h₂.symm
      _ = _ := by
        rw [show e.hom.hom.hom.left ≫ pullback.fst G.X.hom U.hom =
          pullback.fst ((baseChange M.hom).obj G).X.hom p.left ≫ pullback.fst G.X.hom M.hom
          from Descent.pullbackComparison_hom_fst M.hom p.left U.hom p.w G]
  · exact k.hom.hom.w.trans k'.hom.hom.w.symm

private theorem comap_evaluate_overParameter (p : U ⟶ M) (a : Over.mk p.left ⟶ N)
    (l : L ⟶ (baseChange N.hom).obj ((baseChange M.hom).obj G)) :
    (evaluate (pushFamily M.hom l) (overParameter p a)).comap
      (Descent.pullbackComparison M.hom p.left U.hom p.w G).hom = evaluate l a := by
  rw [evaluate, familyHom_overParameter, range_comp_iso,
    ← comap_comp, Iso.hom_inv_id, comap_id]
  rfl

private theorem comap_evaluate_centralizerParameter {C : GroupScheme M.left}
    (c : C ⟶ (baseChange M.hom).obj G) (p : U ⟶ M) :
    (evaluate c p).comap (Descent.pullbackComparison M.hom p.left U.hom p.w G).hom =
      range ((baseChange p.left).map c) := by
  rw [evaluate, familyHom, range_comp_iso, ← comap_comp, Iso.hom_inv_id, comap_id]

private theorem fixedCentralizer_eval {C : GroupScheme M.left}
    (c : C ⟶ (baseChange M.hom).obj G)
    (l : L ⟶ (baseChange N.hom).obj ((baseChange M.hom).obj G))
    (hl : (range l).centralizer = range ((baseChange N.hom).map c))
    {V : Over M.left} (a : V ⟶ N) :
    (evaluate l a).centralizer = range ((baseChange V.hom).map c) := by
  let B := baseChange a.left
  let J := (baseChange M.hom).obj G
  let e := Descent.pullbackComparison N.hom a.left V.hom a.w J
  let cN := (baseChange N.hom).map c
  have h : (range (B.map l)).centralizer = range (B.map cN) := by
    rw [range_baseChangeHom a.left l, range_baseChangeHom a.left cN, ← centralizer_baseChange, hl]
  have he := congrArg (comap e.inv) (centralizer_range_eq_comap_of_iso (B.map l) e)
  rw [← comap_comp, Iso.inv_hom_id, comap_id, h, ← range_comp_iso] at he
  change (range (B.map l ≫ e.hom)).centralizer = _
  rw [← he, Descent.pullbackComparison_naturality N.hom a.left V.hom a.w c, range_iso_comp]

set_option maxHeartbeats 1500000 in
private theorem isUniversal_push_of_fixed (P : SmoothTorusCentralizerParameter G)
    {N : Over P.base.left} {L : GroupScheme N.left}
    (l : L ⟶ (baseChange N.hom).obj ((baseChange P.base.hom).obj G))
    (hl : (range l).centralizer = range ((baseChange N.hom).map P.inclusion))
    (hu : IsUniversalWithFixedCentralizer P.inclusion l) :
    IsUniversal (G := G) (M := (Over.map P.base.hom).obj N) (pushFamily P.base.hom l) := by
  intro U F hF
  obtain ⟨p, hp, hpu⟩ := P.universal U F hF
  let V : Over P.base.left := Over.mk p.left
  let e := Descent.pullbackComparison P.base.hom p.left U.hom p.w G
  let FP := F.comap e.hom
  have hFP : IsAdmissible FP := isAdmissible_comapIso ⟨F, hF⟩ e
  have hFC : FP.centralizer = range ((baseChange V.hom).map P.inclusion) := by
    change (F.comap e.hom).centralizer = _
    rw [centralizer_comap_iso e F hF, ← hp]
    exact comap_evaluate_centralizerParameter P.inclusion p
  obtain ⟨a, ha, hau⟩ := hu V FP hFP hFC
  refine ⟨overParameter p a, ?_, fun b hb => ?_⟩
  · change evaluate (pushFamily P.base.hom l) (overParameter p a) = F
    apply comap_iso_injective e
    rw [comap_evaluate_overParameter]
    exact ha
  · change evaluate (pushFamily P.base.hom l) b = F at hb
    let p' : U ⟶ P.base := Over.homMk (b.left ≫ N.hom) (by
      rw [Category.assoc]
      exact b.w)
    let a' : Over.mk p'.left ⟶ N := Over.homMk b.left rfl
    have hab : overParameter p' a' = b := Over.OverMorphism.ext rfl
    have hp' : evaluate P.inclusion p' = F.centralizer := by
      let e' := Descent.pullbackComparison P.base.hom p'.left U.hom p'.w G
      apply comap_iso_injective e'
      rw [comap_evaluate_centralizerParameter, ← centralizer_comap_iso e' F hF, ← hb, ← hab,
        comap_evaluate_overParameter, fixedCentralizer_eval P.inclusion l hl a']
      rfl
    have hpq : p' = p := hpu p' hp'
    let b' : V ⟶ N := Over.homMk b.left (congrArg (fun f => f.left) hpq)
    have hbb : overParameter p b' = b := Over.OverMorphism.ext rfl
    have hb' : evaluate l b' = FP := by
      rw [← comap_evaluate_overParameter p b' l, hbb, hb]
    exact hbb.symm.trans (congrArg (overParameter p) (hau b' hb'))

/-- The connected noetherian geometric inputs from which the general smooth
representability statement follows. -/
def AffineFiberTorusModuliInputsStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom]
    [IsSeparated G.X.hom] [QuasiCompact G.X.hom] [GeometricallyConnected G.X.hom],
    HasAffineResidueFibers G →
    (∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
      (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)),
        IsAffineHom ((baseChange a).obj G).X.hom) ∧
    AdicLimits (smallAdmissiblePresheaf G) ∧ Nonempty (SmoothTorusCentralizerParameter G)

set_option maxHeartbeats 1500000 in
/-- The connected noetherian inputs produce an actual smooth universal torus
family over an arbitrary base. -/
theorem smoothAffineFiberTorusSubgroupRepresentability_of_moduliInputs
    (h : AffineFiberTorusModuliInputsStatement.{u}) :
    SmoothAffineFiberTorusSubgroupRepresentabilityStatement.{u} := by
  apply smoothAffineFiberTorusSubgroupRepresentability_of_noetherianAffine
  apply noetherianAffineTorusSubgroupRepresentability_of_connected
  intro A _ _ G _ _ _ _ hG
  obtain ⟨hA, hadic, ⟨P⟩⟩ := h A G hG
  let q := P.base.hom
  let G' := (baseChange q).obj G
  have : Smooth q := P.smooth_base
  have : IsLocallyNoetherian P.base.left := LocallyOfFiniteType.isLocallyNoetherian q
  have : Smooth G'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : IsSeparated G'.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : QuasiCompact G'.X.hom := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  have : GeometricallyConnected G'.X.hom :=
    MorphismProperty.pullback_snd (P := @GeometricallyConnected) _ _ inferInstance
  have : Smooth P.group.X.hom := P.smooth_group
  have : GeometricallyConnected P.group.X.hom := P.connected_group
  have hA' (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
      (f : Spec (CommRingCat.of B) ⟶ P.base.left) : IsAffineHom ((baseChange f).obj G').X.hom := by
    let e := (Grp.forget _).mapIso (Descent.pullbackComparison q f (f ≫ q) rfl G)
    have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    have : IsAffineHom ((baseChange (f ≫ q)).obj G).X.hom := hA B (f ≫ q)
    have he : e.hom.left ≫ ((baseChange (f ≫ q)).obj G).X.hom =
        ((baseChange f).obj G').X.hom := e.hom.w
    rw [← he]
    infer_instance
  have ha := admissibleAdicLimits_baseChange q G hadic
  obtain ⟨N, L, l, het, hl, hL, hC, hu⟩ := etaleFixedCentralizerTorusRepresentability G' P.group
    (hG.baseChange q) hA' ha P.inclusion P.closed
  refine ⟨(Over.map q).obj N, L, pushFamily q l, isClosedSubgroup_pushFamily q l hl, hL,
    isUniversal_push_of_fixed P l hC hu, ?_⟩
  change Smooth (N.hom ≫ q)
  infer_instance

end Langlands.GroupScheme.TorusSubgroupModuli
