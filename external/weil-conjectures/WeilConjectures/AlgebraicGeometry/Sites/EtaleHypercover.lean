/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Cohomology
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.FilteredColimitSections
public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Refinement
public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Map

/-!
# Étale hypercovers of quasi-compact quasi-separated schemes

Let `X` be a quasi-compact quasi-separated scheme. A *qcqs hypercover* of `X` is a
semi-simplicial hypercover `U` of the small étale site of `X` all of whose terms `U_n` are
quasi-compact and quasi-separated (`AlgebraicGeometry.Scheme.IsQcqsHypercover`).

Local lifting requirements can be met after refinement within qcqs hypercovers
(`AlgebraicGeometry.Scheme.IsQcqsHypercover.exists_refinement_lift`). Hence the étale
cohomology of `X` with coefficients in sheaves of `Λ`-modules is computed by qcqs hypercovers
(`AlgebraicGeometry.Scheme.exists_cohomologyClass_eq_of_isQcqsHypercover`,
`AlgebraicGeometry.Scheme.exists_isCoboundary_of_isQcqsHypercover`).

We also record the behaviour of hypercovers and of their cohomology classes under base change
along a morphism `g : Y ⟶ X`.

## Implementation details

We work with semi-simplicial hypercovers (face maps only), which is all the computation of
cohomology uses. In the refinement, a section of a quotient sheaf over `U_p` lifts after
replacing `U_p` by a finite disjoint union of affine étale schemes on which it lifts, and the
higher terms by the relative coskeleta `M_k(V) ×_{M_k(U)} U_k`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A *qcqs hypercover* of `X`: a semi-simplicial hypercover of the small étale site of `X` all of
whose terms are quasi-compact and quasi-separated. -/
structure IsQcqsHypercover (U : SemiSimplicialObject X.Etale) : Prop where
  isHypercover : U.IsHypercover X.smallEtaleTopology
  compactSpace (n : ℕ) : CompactSpace (U.obj n).left
  quasiSeparatedSpace (n : ℕ) : QuasiSeparatedSpace (U.obj n).left

section Qcqs

variable (X) in
/-- The étale `X`-schemes with quasi-compact quasi-separated underlying scheme. -/
def etaleQcqs : ObjectProperty X.Etale :=
  fun V ↦ CompactSpace V.left ∧ QuasiSeparatedSpace V.left

instance : (etaleQcqs X).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ compactSpace_and_quasiSeparatedSpace_of_iso e h⟩

instance [CompactSpace X] [QuasiSeparatedSpace X] :
    (etaleQcqs X).IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := ⟨by
  rintro A ⟨h⟩
  have hA : IsTerminal A := (isLimitEquivIsTerminalOfIsEmpty _ _) h.isLimit
  exact compactSpace_and_quasiSeparatedSpace_of_iso
    ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X).uniqueUpToIso hA)
    ⟨‹_›, ‹_›⟩⟩

instance : (etaleQcqs X).IsClosedUnderLimitsOfShape WalkingCospan := ⟨by
  rintro A ⟨h⟩
  obtain ⟨_, _⟩ := h.prop_diag_obj .left
  obtain ⟨_, _⟩ := h.prop_diag_obj .right
  obtain ⟨_, _⟩ := h.prop_diag_obj .one
  let e : A ≅ pullback (h.diag.map WalkingCospan.Hom.inl) (h.diag.map WalkingCospan.Hom.inr) :=
    h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _)
  exact compactSpace_and_quasiSeparatedSpace_of_iso e.symm
    (compactSpace_and_quasiSeparatedSpace_pullback _ _)⟩

instance [CompactSpace X] [QuasiSeparatedSpace X] (J : Type) [SmallCategory J] [FinCategory J] :
    (etaleQcqs X).IsClosedUnderLimitsOfShape J :=
  (etaleQcqs X).isClosedUnderLimitsOfShape_of_terminal_of_pullback J

instance [CompactSpace X] [QuasiSeparatedSpace X] : (etaleQcqs X).IsClosedUnderFiniteProducts :=
  (etaleQcqs X).isClosedUnderFiniteProducts_of_terminal_of_pullback

end Qcqs

section Lift

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- An étale sheaf of `Λ`-modules has at most one section over an étale `X`-scheme with empty
underlying scheme. -/
lemma subsingleton_obj_of_isEmpty_moduleCat (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Z : X.Etale} (hZ : IsEmpty Z.left) : Subsingleton (F.obj.obj (op Z)) :=
  ⟨fun _ _ ↦ (isSheafFor_ofArrows_moduleCat F (U := (PEmpty.elim : PEmpty.{1} → X.Etale))
    (fun a ↦ a.elim) (Set.eq_univ_of_forall fun z ↦ isEmptyElim z)).isSeparatedFor.ext
    fun _ _ ⟨a⟩ ↦ a.elim⟩

/-- **Local lifting through an epimorphism, with a single qcqs cover.** If `V` is an étale
`X`-scheme with quasi-compact underlying scheme and `φ : G ⟶ Q` is an epimorphism of étale sheaves
of `Λ`-modules, every section of `Q` over `V` lifts to `G` after pullback along a single covering
`W ⟶ V` by an étale `X`-scheme with affine (hence qcqs) underlying scheme: a finite disjoint
union of affine étale schemes over which the section lifts. -/
lemma exists_cover_lift {V : X.Etale} [CompactSpace V.left]
    {G Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : G ⟶ Q) [Epi φ]
    (w : Q.obj.obj (op V)) :
    ∃ (W : X.Etale) (π : W ⟶ V), etaleQcqs X W ∧
      Sieve.ofArrows (fun _ : Unit ↦ W) (fun _ ↦ π) ∈ X.smallEtaleTopology V ∧
      ∃ w' : G.obj.obj (op W), (φ.hom.app _).hom w' = (Q.obj.map π.op).hom w := by
  have hφ : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 ‹_›
  obtain ⟨n, U, g, hg, hU, hcov⟩ :=
    (AlgebraicGeometry.Etale.exists_affine_refinement _) (hφ.imageSieve_mem w)
  choose t ht using hg
  have : Etale (Sigma.desc fun a ↦ (U a).hom) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @AlgebraicGeometry.Etale) fun a ↦ (U a).prop
  let W : X.Etale := Etale.mk (Sigma.desc fun a ↦ (U a).hom)
  let ι (a : Fin n) : U a ⟶ W :=
    MorphismProperty.Over.homMk (Sigma.ι (fun a ↦ (U a).left) a) (by simp [W])
  let π : W ⟶ V := MorphismProperty.Over.homMk (Sigma.desc fun a ↦ (g a).left)
    (Sigma.hom_ext _ _ fun a ↦ by simp [W])
  have hιπ (a : Fin n) : ι a ≫ π = g a :=
    MorphismProperty.Over.Hom.ext (Sigma.ι_comp_desc _ a)
  have hιcov : ⋃ a, Set.range (ι a).left = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨y, hy⟩ := (sigmaOpenCover fun a ↦ (U a).left).covers x
    exact Set.mem_iUnion.2 ⟨_, y, hy⟩
  have : IsAffine W.left := inferInstanceAs (IsAffine (∐ fun a ↦ (U a).left))
  refine ⟨W, π, ⟨inferInstance, inferInstance⟩, ?_, ?_⟩
  · refine (ofArrows_mem_smallEtaleTopology_iff _).2 (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨_, ⟨a, rfl⟩, y, rfl⟩ := hcov.symm ▸ Set.mem_univ x
    refine Set.mem_iUnion.2 ⟨⟨⟩, (ι a).left y, ?_⟩
    rw [← hιπ a]
    rfl
  · obtain ⟨w', hw'⟩ := ((Presieve.isSheafFor_arrows_iff _ _).1
      (isSheafFor_ofArrows_moduleCat G ι hιcov)) (fun a ↦ t a) (by
        intro a b Z ga gb h
        by_cases hab : a = b
        · subst hab
          have : ga = gb := MorphismProperty.Over.Hom.ext
            ((cancel_mono (Sigma.ι (fun a ↦ (U a).left) a)).1
              (congrArg (fun f ↦ f.left) h))
          rw [this]
        · have : IsEmpty Z.left := isEmpty_of_commSq_sigmaι_of_ne
            ⟨congrArg (fun f ↦ f.left) h⟩ hab
          exact (subsingleton_obj_of_isEmpty_moduleCat G this).elim _ _)
    refine ⟨w', (isSheafFor_ofArrows_moduleCat Q ι hιcov).isSeparatedFor.ext fun _ _ ⟨a⟩ ↦ ?_⟩
    change (Q.obj.map (ι a).op).hom ((φ.hom.app _).hom w') =
      (Q.obj.map (ι a).op).hom ((Q.obj.map π.op).hom w)
    rw [← NatTrans.naturality_apply φ.hom, show (G.obj.map (ι a).op).hom w' = t a from hw'.1 a,
      ht a, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hιπ]

end Lift
/-- A quasi-compact quasi-separated scheme has a qcqs hypercover: the constant one on the terminal
object. -/
lemma exists_isQcqsHypercover [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ U : SemiSimplicialObject X.Etale, IsQcqsHypercover U :=
  ⟨_, ⟨SemiSimplicialObject.isHypercover_const _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X),
    fun _ ↦ inferInstanceAs (CompactSpace X), fun _ ↦ inferInstanceAs (QuasiSeparatedSpace X)⟩⟩

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Local lifting after refinement**: a
section of a quotient sheaf over a term `U_p` of a qcqs hypercover lifts, after refinement of the
hypercover within qcqs hypercovers. -/
theorem IsQcqsHypercover.exists_refinement_lift [CompactSpace X] [QuasiSeparatedSpace X]
    {U : SemiSimplicialObject X.Etale} (hU : IsQcqsHypercover U) (p : ℕ)
    {G Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : G ⟶ Q) [Epi φ]
    (w : Q.obj.obj (op (U.obj p))) :
    ∃ (V : SemiSimplicialObject X.Etale) (_ : IsQcqsHypercover V) (f : V ⟶ U)
      (w' : G.obj.obj (op (V.obj p))), (φ.hom.app _).hom w' = (Q.obj.map (f.app p).op).hom w := by
  have := hU.compactSpace p
  obtain ⟨Wp, πp, hWp, hcov, w', hw'⟩ := exists_cover_lift φ w
  let fam (k : ℕ) : Σ W : X.Etale, W ⟶ U.obj k :=
    if h : k = p then ⟨Wp, πp ≫ eqToHom (congrArg U.obj h.symm)⟩ else ⟨U.obj k, 𝟙 _⟩
  have hfam (k : ℕ) : etaleQcqs X (fam k).1 ∧
      Sieve.ofArrows (fun _ : Unit ↦ (fam k).1) (fun _ ↦ (fam k).2) ∈
        X.smallEtaleTopology (U.obj k) := by
    by_cases h : k = p
    · subst h
      rw [show fam k = ⟨Wp, πp ≫ eqToHom rfl⟩ from dite_eq_left rfl]
      simpa using ⟨hWp, hcov⟩
    · rw [show fam k = ⟨U.obj k, 𝟙 _⟩ from dite_eq_right h]
      refine ⟨⟨hU.compactSpace k, hU.quasiSeparatedSpace k⟩, ?_⟩
      refine (X.smallEtaleTopology).superset_covering (fun _ g _ ↦ ?_)
        ((X.smallEtaleTopology).top_mem _)
      exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨⟩, g, (Category.comp_id g).symm⟩
  let V := SemiSimplicialObject.refinement U (fun k ↦ (fam k).1) (fun k ↦ (fam k).2)
  have hV : IsQcqsHypercover V :=
    { isHypercover := hU.isHypercover.refinement fun k ↦ (hfam k).2
      compactSpace k := (SemiSimplicialObject.refinement_obj_prop (etaleQcqs X)
        (fun k ↦ ⟨hU.compactSpace k, hU.quasiSeparatedSpace k⟩) (fun k ↦ (hfam k).1) k).1
      quasiSeparatedSpace k := (SemiSimplicialObject.refinement_obj_prop (etaleQcqs X)
        (fun k ↦ ⟨hU.compactSpace k, hU.quasiSeparatedSpace k⟩) (fun k ↦ (hfam k).1) k).2 }
  refine ⟨V, hV, SemiSimplicialObject.refinementHom _ _ _, ?_⟩
  have key : ∀ s : Σ W : X.Etale, W ⟶ U.obj p, s = ⟨Wp, πp ≫ eqToHom rfl⟩ →
      ∀ ρ : V.obj p ⟶ s.1, ρ ≫ s.2 = (SemiSimplicialObject.refinementHom _ _ _).app p →
      ∃ w'' : G.obj.obj (op (V.obj p)), (φ.hom.app _).hom w'' =
        (Q.obj.map ((SemiSimplicialObject.refinementHom _ _ _).app p).op).hom w := by
    rintro s rfl ρ hρ
    refine ⟨(G.obj.map ρ.op).hom w', ?_⟩
    rw [← hρ, eqToHom_refl, Category.comp_id, NatTrans.naturality_apply φ.hom, hw', op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply]
  exact key _ (dite_eq_left rfl) _ (SemiSimplicialObject.refinementToW_π _ _ _ p)

/-- **Étale cohomology is computed by qcqs hypercovers**: every class is the class of a cocycle
on a qcqs hypercover. -/
theorem exists_cohomologyClass_eq_of_isQcqsHypercover [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (x : Ext (SemiSimplicialObject.constSheaf X.smallEtaleTopology Λ) F q) :
    ∃ (U : SemiSimplicialObject X.Etale) (hU : IsQcqsHypercover U) (z : F.obj.obj (op (U.obj q)))
      (hz : U.IsCocycle F q z), hU.isHypercover.cohomologyClass F q z hz = x :=
  SemiSimplicialObject.exists_cohomologyClass_eq IsQcqsHypercover (fun _ hU ↦ hU.isHypercover)
    exists_isQcqsHypercover (fun _ hU p _ _ φ _ w ↦ hU.exists_refinement_lift Λ p φ w) F q x

/-- **A hypercover cocycle with vanishing class is a coboundary after refinement** within qcqs
hypercovers. -/
theorem exists_isCoboundary_of_isQcqsHypercover [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    {U : SemiSimplicialObject X.Etale} (hU : IsQcqsHypercover U) (z : F.obj.obj (op (U.obj q)))
    (hz : U.IsCocycle F q z) (h : hU.isHypercover.cohomologyClass F q z hz = 0) :
    ∃ (V : SemiSimplicialObject X.Etale) (_ : IsQcqsHypercover V) (f : V ⟶ U),
      V.IsCoboundary F q ((F.obj.map (f.app q).op).hom z) :=
  SemiSimplicialObject.exists_isCoboundary_of_cohomologyClass_eq_zero IsQcqsHypercover
    (fun _ hU ↦ hU.isHypercover) (fun _ hU p _ _ φ _ w ↦ hU.exists_refinement_lift Λ p φ w)
    F q U hU z hz h

section BaseChange

variable {Y : Scheme.{u}} (g : Y ⟶ X)

/-- The base change `U ×_X Y` of a semi-simplicial étale `X`-scheme along `g : Y ⟶ X`. -/
noncomputable abbrev _root_.CategoryTheory.SemiSimplicialObject.baseChange
    (U : SemiSimplicialObject X.Etale) : SemiSimplicialObject Y.Etale :=
  U.map (MorphismProperty.Over.pullback @Etale ⊤ g)

/-- Base change of hypercovers. -/
lemma _root_.CategoryTheory.SemiSimplicialObject.IsHypercover.baseChange
    {U : SemiSimplicialObject X.Etale} (hU : U.IsHypercover X.smallEtaleTopology) :
    (U.baseChange g).IsHypercover Y.smallEtaleTopology :=
  hU.map (Scheme.Hom.coverPreserving_etale g)

/-- Base change of qcqs hypercovers along a quasi-compact quasi-separated morphism. -/
lemma IsQcqsHypercover.baseChange [QuasiCompact g] [QuasiSeparated g]
    {U : SemiSimplicialObject X.Etale} (hU : IsQcqsHypercover U) :
    IsQcqsHypercover (U.baseChange g) := by
  have h (n : ℕ) : CompactSpace ((U.baseChange g).obj n).left ∧
      QuasiSeparatedSpace ((U.baseChange g).obj n).left := by
    rw [show ((U.baseChange g).obj n).left = Limits.pullback (U.obj n).hom g from rfl]
    have := hU.compactSpace n
    have := hU.quasiSeparatedSpace n
    have : CompactSpace ((𝟭 Scheme).obj (U.obj n).left) :=
      inferInstanceAs (CompactSpace (U.obj n).left)
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj (U.obj n).left) :=
      inferInstanceAs (QuasiSeparatedSpace (U.obj n).left)
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst (U.obj n).hom g),
      quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.fst (U.obj n).hom g)⟩
  exact ⟨hU.isHypercover.baseChange g, fun n ↦ (h n).1, fun n ↦ (h n).2⟩

/-- The pullback of a section of `F` over an étale `X`-scheme `V` to a section of `g^* F` over
`V ×_X Y`: the unit `F ⟶ g_* g^* F` evaluated at `V`. -/
noncomputable def _root_.AlgebraicGeometry.Etale.modulePullbackSection
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale) :
    F.obj.obj (op V) →ₗ[Λ] ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) :=
  (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F).hom.app
    (op V)).hom


/-- Naturality of `Etale.modulePullbackSection` in the sheaf. -/
lemma _root_.AlgebraicGeometry.Etale.modulePullbackSection_naturality
    {F F' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ F') (V : X.Etale)
    (s : F.obj.obj (op V)) :
    (((Etale.upperStar (ModuleCat.{u + 1} Λ) g).map φ).hom.app _).hom
        (Etale.modulePullbackSection Λ g F V s) =
      Etale.modulePullbackSection Λ g F' V ((φ.hom.app _).hom s) := by
  have h := congrArg (fun k ↦ (k.hom.app (op V)).hom s)
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.naturality φ)
  exact h.symm

/-- Naturality of `Etale.modulePullbackSection` in the étale `X`-scheme. -/
lemma _root_.AlgebraicGeometry.Etale.modulePullbackSection_map
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V V' : X.Etale} (a : V' ⟶ V)
    (s : F.obj.obj (op V)) :
    (((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ g).map a).op).hom
        (Etale.modulePullbackSection Λ g F V s) =
      Etale.modulePullbackSection Λ g F V' ((F.obj.map a.op).hom s) := by
  have h := congrArg (fun k ↦ k.hom s)
    (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F).hom.naturality
      a.op)
  exact h.symm


/-- The section `1` of the constant sheaf `Λ` over an étale `S`-scheme. -/
noncomputable abbrev _root_.AlgebraicGeometry.Etale.constSheafOne {S : Scheme.{u}} (V : S.Etale) :
    (SemiSimplicialObject.constSheaf S.smallEtaleTopology Λ).obj.obj (op V) :=
  ((toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj
    (ModuleCat.of Λ Λ))).app (op V)).hom (1 : Λ)

lemma _root_.AlgebraicGeometry.Etale.constSheafOne_map {S : Scheme.{u}} {V V' : S.Etale}
    (a : V' ⟶ V) :
    ((SemiSimplicialObject.constSheaf S.smallEtaleTopology Λ).obj.map a.op).hom
      (Etale.constSheafOne Λ V) = Etale.constSheafOne Λ V' :=
  (congrArg (fun k ↦ k.hom (1 : Λ))
    ((toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj
      (ModuleCat.of Λ Λ))).naturality a.op)).symm

/-- The isomorphism `g^* Λ ≅ Λ` maps the pullback of the section `1` over `X` to the section `1`
over `X ×_X Y`. -/
lemma _root_.AlgebraicGeometry.Etale.constantSheafCompUpperStarIso_hom_modulePullbackSection_one :
    (((Etale.constantSheafCompUpperStarIso Λ g).app (ModuleCat.of Λ Λ)).hom.hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj (Scheme.Etale.mk (𝟙 X))))).hom
      (Etale.modulePullbackSection Λ g _ _ (Etale.constSheafOne Λ (Scheme.Etale.mk (𝟙 X)))) =
      Etale.constSheafOne Λ
        ((MorphismProperty.Over.pullback @Etale ⊤ g).obj (Scheme.Etale.mk (𝟙 X))) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).comp
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)).ofNatIsoRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)))
    (constantSheafAdj _ _ (Etale.isTerminalOverPullbackObjMkId g)) (ModuleCat.of Λ Λ)
  exact congrArg (fun k ↦ k.hom (1 : Λ)) h

/-- The isomorphism `Λ ≅ g^* Λ` maps the section `1` over `V ×_X Y` to the pullback of the
section `1` over `V`. -/
lemma _root_.AlgebraicGeometry.Etale.constantSheafCompUpperStarIso_inv_one (V : X.Etale) :
    (((Etale.constantSheafCompUpperStarIso Λ g).app (ModuleCat.of Λ Λ)).inv.hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V))).hom
      (Etale.constSheafOne Λ ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) =
      Etale.modulePullbackSection Λ g _ V (Etale.constSheafOne Λ V) := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let t : V ⟶ T := (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X).from V
  let e := (Etale.constantSheafCompUpperStarIso Λ g).app (ModuleCat.of Λ Λ)
  rw [← Etale.constSheafOne_map Λ ((MorphismProperty.Over.pullback @Etale ⊤ g).map t),
    ← Etale.constSheafOne_map Λ t, ← Etale.modulePullbackSection_map]
  refine (congrArg (fun k ↦ k.hom (Etale.constSheafOne Λ
    ((MorphismProperty.Over.pullback @Etale ⊤ g).obj T)))
    (e.inv.hom.naturality ((MorphismProperty.Over.pullback @Etale ⊤ g).map t).op)).trans ?_
  simp only [Functor.comp_obj, ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  rw [← Etale.constantSheafCompUpperStarIso_hom_modulePullbackSection_one]
  exact congrArg (fun k ↦ (k.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj T))).hom
    (Etale.modulePullbackSection Λ g _ _ (Etale.constSheafOne Λ T))) e.hom_inv_id

open SemiSimplicialObject in
/-- The section of the constant sheaf corresponding to the augmentation `Λ[V] ⟶ Λ` is `1`. -/
lemma _root_.AlgebraicGeometry.Etale.freeSheafHomEquiv_map_freeYonedaToConst {S : Scheme.{u}}
    (V : S.Etale) :
    freeSheafHomEquiv S.smallEtaleTopology Λ V (constSheaf _ Λ)
      ((presheafToSheaf _ _).map (freeYonedaToConst Λ V)) = Etale.constSheafOne Λ V := by
  have h1 : (sheafificationAdjunction S.smallEtaleTopology _).homEquiv _ (constSheaf _ Λ)
      ((presheafToSheaf _ _).map (freeYonedaToConst Λ V)) =
      freeYonedaToConst Λ V ≫ toSheafify _ _ := by
    rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
    exact (toSheafify_naturality _ (freeYonedaToConst Λ V)).symm
  simp only [freeSheafHomEquiv, Equiv.trans_apply]
  erw [h1]
  change ((freeYonedaToConst Λ V ≫ toSheafify _ _).app (op V)).hom
    (Finsupp.single (ULift.up (𝟙 V)) (1 : Λ)) = _
  simp only [freeYonedaToConst, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom]
  congr 1
  erw [Finsupp.linearCombination_single]
  exact one_smul _ _
open SemiSimplicialObject in
/-- The comparison map `Λ[V ×_X Y] ⟶ g^* Λ[V]` of free sheaves: it corresponds to the pullback
of the tautological section of `Λ[V]` over `V`. -/
noncomputable def _root_.AlgebraicGeometry.Etale.freeSheafBaseChange (V : X.Etale) :
    (freeSheaf Y.smallEtaleTopology Λ).obj ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V) ⟶
      (Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj ((freeSheaf X.smallEtaleTopology Λ).obj V) :=
  (freeSheafHomEquiv _ _ _ _).symm (Etale.modulePullbackSection Λ g _ V
    (freeSheafHomEquiv _ _ _ _ (𝟙 _)))

open SemiSimplicialObject in
lemma _root_.AlgebraicGeometry.Etale.freeSheafHomEquiv_freeSheafBaseChange_comp (V : X.Etale)
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : (freeSheaf X.smallEtaleTopology Λ).obj V ⟶ M) :
    freeSheafHomEquiv _ _ _ _
        (Etale.freeSheafBaseChange Λ g V ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) g).map φ) =
      Etale.modulePullbackSection Λ g M V (freeSheafHomEquiv _ _ _ _ φ) := by
  rw [freeSheafHomEquiv_comp, Etale.freeSheafBaseChange, Equiv.apply_symm_apply,
    Etale.modulePullbackSection_naturality, ← freeSheafHomEquiv_comp, Category.id_comp]

open SemiSimplicialObject in
lemma _root_.AlgebraicGeometry.Etale.map_comp_freeSheafBaseChange {V V' : X.Etale}
    (a : V' ⟶ V) :
    (freeSheaf Y.smallEtaleTopology Λ).map ((MorphismProperty.Over.pullback @Etale ⊤ g).map a) ≫
        Etale.freeSheafBaseChange Λ g V =
      Etale.freeSheafBaseChange Λ g V' ≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g).map
          ((freeSheaf X.smallEtaleTopology Λ).map a) := by
  apply (freeSheafHomEquiv _ _ _ _).injective
  rw [freeSheafHomEquiv_map_comp, Etale.freeSheafHomEquiv_freeSheafBaseChange_comp,
    Etale.freeSheafBaseChange, Equiv.apply_symm_apply, Etale.modulePullbackSection_map,
    ← freeSheafHomEquiv_map_comp, Category.comp_id]

open SemiSimplicialObject in
/-- The comparison morphism `Λ[U_• ×_X Y] ⟶ g^* Λ[U_•]` of free complexes. -/
noncomputable def _root_.AlgebraicGeometry.Etale.freeComplexBaseChange
    (U : SemiSimplicialObject X.Etale) :
    (U.baseChange g).freeComplex Y.smallEtaleTopology Λ ⟶
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapHomologicalComplex _).obj
        (U.freeComplex X.smallEtaleTopology Λ) where
  f n := Etale.freeSheafBaseChange Λ g (U.obj n)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [Functor.mapHomologicalComplex_obj_d, freeComplex_d, freeComplex_d, Functor.map_sum,
      Preadditive.comp_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    congr 1
    exact (Etale.map_comp_freeSheafBaseChange Λ g (U.δ j k)).symm

open SemiSimplicialObject in
/-- The comparison of free sheaves is compatible with the augmentations to the constant sheaves
and the isomorphism `g^* Λ ≅ Λ`. -/
lemma _root_.AlgebraicGeometry.Etale.freeAugmentation_baseChange (V : X.Etale) :
    (presheafToSheaf _ _).map
        (freeYonedaToConst Λ ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) ≫
      ((Etale.constantSheafCompUpperStarIso Λ g).app (ModuleCat.of Λ Λ)).inv =
      Etale.freeSheafBaseChange Λ g V ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) g).map
        ((presheafToSheaf _ _).map (freeYonedaToConst Λ V)) := by
  apply (freeSheafHomEquiv Y.smallEtaleTopology Λ
    ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V) _).injective
  rw [freeSheafHomEquiv_comp]
  erw [Etale.freeSheafHomEquiv_map_freeYonedaToConst]
  refine (Etale.constantSheafCompUpperStarIso_inv_one Λ g V).trans ?_
  rw [← Etale.freeSheafHomEquiv_map_freeYonedaToConst]
  exact (Etale.freeSheafHomEquiv_freeSheafBaseChange_comp Λ g V _).symm

/-- The restriction map `H^q(X, F) ⟶ H^q(Y, g^* F)` of étale cohomology along `g : Y ⟶ X`:
pull back extension classes along the exact functor `g^*`, which preserves the constant sheaf
`Λ`. -/
noncomputable def _root_.AlgebraicGeometry.Etale.cohomologyRestrict
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Ext (SemiSimplicialObject.constSheaf X.smallEtaleTopology Λ) F q →+
      Ext (SemiSimplicialObject.constSheaf Y.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F) q :=
  AddMonoidHom.mk' (fun x ↦
    (Ext.mk₀ ((Etale.constantSheafCompUpperStarIso Λ g).app (ModuleCat.of Λ Λ)).inv).comp
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapExtAddHom _ _ q x) (zero_add q))
    (fun x y ↦ by rw [map_add, Ext.comp_add])

/-- Base change is compatible with classes of hypercover cocycles. -/
theorem _root_.AlgebraicGeometry.Etale.cohomologyRestrict_cohomologyClass
    {U : SemiSimplicialObject X.Etale} (hU : U.IsHypercover X.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (z : F.obj.obj (op (U.obj q)))
    (hz : U.IsCocycle F q z) :
    Etale.cohomologyRestrict Λ g F q (hU.cohomologyClass F q z hz) =
      (hU.baseChange g).cohomologyClass _ q (Etale.modulePullbackSection Λ g F (U.obj q) z)
        (hz.map ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F)) := by
  have hK := hU.isResolution (R := Λ)
  have hK' := (hU.baseChange g).isResolution (R := Λ)
  let G := Etale.upperStar (ModuleCat.{u + 1} Λ) g
  let φ := (SemiSimplicialObject.freeSheafHomEquiv _ _ (U.obj q) F).symm z
  let c := Etale.freeComplexBaseChange Λ g U
  have hcφ : c.f q ≫ G.map φ = (SemiSimplicialObject.freeSheafHomEquiv _ _ _ _).symm
      (Etale.modulePullbackSection Λ g F (U.obj q) z) := by
    apply (SemiSimplicialObject.freeSheafHomEquiv _ _ _ _).injective
    refine (Etale.freeSheafHomEquiv_freeSheafBaseChange_comp Λ g _ φ).trans ?_
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change (Ext.mk₀ _).comp ((hU.cohomologyClass F q z hz).mapExactFunctor G) (zero_add q) = _
  rw [SemiSimplicialObject.IsHypercover.cohomologyClass, hK.mapExt_cocycleClass G,
    SemiSimplicialObject.IsHypercover.cohomologyClass]
  refine Eq.symm ((hK.map G).splicing_extClass_comp_mk₀ hK'.splicing c.f _ ?_ ?_ q (G.map φ) _
    (hK'.desc q _ _) ?_)
  · exact Etale.freeAugmentation_baseChange Λ g (U.obj 0)
  · intro n
    simp only [ChainComplex.IsResolution.splicing_g, ChainComplex.IsResolution.splicing_f]
    rw [reassoc_of% (hK'.π_ι n), c.comm]
  · simp only [ChainComplex.IsResolution.splicing_g, ChainComplex.IsResolution.π_desc]
    exact hcφ.symm

end BaseChange

end AlgebraicGeometry.Scheme
