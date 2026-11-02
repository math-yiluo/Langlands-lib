import Langlands.AlgebraicGeometry.Modules.StalkIsoLocus
import Langlands.AlgebraicGeometry.Modules.RestrictionStalkLinearEquiv
import Langlands.AlgebraicGeometry.Modules.FinitePresentationPullback
import Langlands.AlgebraicGeometry.Modules.RankOneStalkReflection

/-! # Descent of local finite presentation along fppf coverings -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}}

section Assembly

/-- A module sheaf with a finite presentation on an open neighbourhood of every point is
locally finitely presented. -/
lemma isFinitePresentation_of_forall_exists_presentation (M : Y.Modules)
    (H : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∃ P : (M.restrict U.ι).Presentation, P.IsFinite) :
    M.IsFinitePresentation := by
  choose U hyU P hP using H
  let q : M.QuasicoherentData :=
    { I := Y
      X := U
      coversTop := by
        apply (_root_.Opens.coversTop_iff Y _).2
        apply top_le_iff.mp
        intro y _
        exact Opens.mem_iSup.mpr ⟨y, hyU y⟩
      presentation := fun y => presentationOverOfRestrict M (U y) (P y) }
  refine SheafOfModules.IsFinitePresentation.mk.{u, u, u} (M := M) ⟨q, ?_⟩
  constructor
  intro y
  have := hP y
  dsimp [q]
  infer_instance

/-- A finite presentation of the restriction along an open immersion gives one on its
open image. -/
lemma exists_presentation_opensRange (M : Y.Modules) {V : Scheme.{u}} (g : V ⟶ Y)
    [IsOpenImmersion g] (P : (M.restrict g).Presentation) [P.IsFinite] :
    ∃ P' : (M.restrict g.opensRange.ι).Presentation, P'.IsFinite :=
  ⟨presentationRestrictOfFac M g g.isoOpensRange.inv g.opensRange.ι
    (Scheme.Hom.isoOpensRange_inv_comp g) P, inferInstance⟩

/-- A global finite presentation makes a module sheaf locally finitely presented. -/
lemma isFinitePresentation_of_presentation {M : X.Modules} (P : M.Presentation)
    [P.IsFinite] : M.IsFinitePresentation :=
  isFinitePresentation_of_forall_exists_presentation M fun _ =>
    ⟨⊤, trivial, Scheme.Modules.presentationRestrict (⊤ : X.Opens).ι P, by
      dsimp [Scheme.Modules.presentationRestrict]; infer_instance⟩

/-- The sheaf associated to a finitely presented module has a finite presentation. -/
lemma exists_presentation_tilde {A : CommRingCat.{u}} (N : ModuleCat.{u} A)
    [Module.FinitePresentation A N] : ∃ P : (tilde N).Presentation, P.IsFinite := by
  obtain ⟨s₀, hs⟩ := Module.Finite.fg_top (R := A) (M := N)
  let s : Set N := s₀
  let f := Finsupp.linearCombination A ((↑) : s → N)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, Subtype.range_coe]
    exact hs
  obtain ⟨t₀, ht⟩ := Module.FinitePresentation.fg_ker f hf
  let t : Set (s →₀ A) := t₀
  exact ⟨presentationTilde N s hs t ht,
    { isFiniteType_generators := ⟨(inferInstance : Finite s)⟩
      isFiniteType_relations := ⟨(inferInstance : Finite t)⟩ }⟩

end Assembly

section Lifting

lemma mem_iInf_of_finite {T : Type*} [TopologicalSpace T] {ι : Type*} [Finite ι]
    {U : ι → Opens T} {x : T} (h : ∀ i, x ∈ U i) : x ∈ ⨅ i, U i := by
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact h

/-- Finitely many elements of a module stalk are germs of sections over one common open
neighbourhood. -/
lemma exists_forall_germ_eq (M : Y.Modules) (y : Y) {ι : Type*} [Finite ι]
    (e : ι → stalk M y) :
    ∃ (U : Y.Opens) (hU : y ∈ U) (s : ι → Γ(M, U)),
      ∀ i, M.presheaf.germ U y hU (s i) = e i := by
  choose U hU s hs using fun i => M.presheaf.exists_germ_eq (e i)
  refine ⟨⨅ i, U i, mem_iInf_of_finite hU,
    fun i => M.presheaf.map (homOfLE (iInf_le U i)).op (s i), fun i => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply]
  exact hs i

/-- Finitely many elements of a local ring are germs of functions over one common open
neighbourhood. -/
lemma exists_forall_germ_eq_ring (y : Y) {ι : Type*} [Finite ι]
    (e : ι → Y.presheaf.stalk y) :
    ∃ (U : Y.Opens) (hU : y ∈ U) (r : ι → Γ(Y, U)),
      ∀ i, Y.presheaf.germ U y hU (r i) = e i := by
  choose U hU r hr using fun i => Y.presheaf.exists_germ_eq (e i)
  refine ⟨⨅ i, U i, mem_iInf_of_finite hU,
    fun i => Y.presheaf.map (homOfLE (iInf_le U i)).op (r i), fun i => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply]
  exact hr i

/-- Finitely many sections with vanishing germ vanish on one common open neighbourhood. -/
lemma exists_le_forall_map_eq_zero (M : Y.Modules) {V : Y.Opens} {y : Y} (hyV : y ∈ V)
    {ι : Type*} [Finite ι] (t : ι → Γ(M, V))
    (ht : ∀ i, M.presheaf.germ V y hyV (t i) = 0) :
    ∃ (W : Y.Opens) (hWV : W ≤ V), y ∈ W ∧
      ∀ i, M.presheaf.map (homOfLE hWV).op (t i) = 0 := by
  have h' : ∀ i, ∃ (W : Y.Opens) (_ : y ∈ W) (hWV : W ≤ V),
      M.presheaf.map (homOfLE hWV).op (t i) = 0 := by
    intro i
    obtain ⟨W, hyW, iU, iV, e⟩ :=
      M.presheaf.germ_eq y hyV hyV (t i) 0 (by rw [ht i, map_zero])
    rw [map_zero] at e
    exact ⟨W, hyW, leOfHom iU, e⟩
  choose W hyW hWV hW using h'
  refine ⟨V ⊓ ⨅ i, W i, inf_le_left, ⟨hyV, mem_iInf_of_finite hyW⟩, fun i => ?_⟩
  have hle : V ⊓ ⨅ i, W i ≤ W i := inf_le_right.trans (iInf_le W i)
  have := congrArg (M.presheaf.map (homOfLE hle).op) (hW i)
  rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
  exact this

end Lifting

section Chart

variable {A : CommRingCat.{u}} (h : Spec A ⟶ Y) [IsOpenImmersion h]

/-- On a spectrum chart, the coordinate-ring action on global sections of the restriction
is the action of the corresponding functions on the image. -/
lemma restrict_smul_Spec (M : Y.Modules) (r : Γ(Y, h ''ᵁ ⊤))
    (m : moduleSpecΓFunctor.obj (M.restrict h)) :
    (Scheme.ΓSpecIso A).hom ((h.appIso ⊤).hom r) • m =
      (show Γ(M, h ''ᵁ ⊤) from r • (show Γ(M, h ''ᵁ ⊤) from m)) := by
  have e1 : (Spec A).presheaf.map (⊤ : (Spec A).Opens).leTop.op
      ((Scheme.ΓSpecIso A).inv ((Scheme.ΓSpecIso A).hom ((h.appIso ⊤).hom r))) =
        (h.appIso ⊤).hom r := by
    rw [Iso.hom_inv_id_apply,
      show (⊤ : (Spec A).Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  have e2 : (h.appIso ⊤).inv ((h.appIso ⊤).hom r) = r := Iso.hom_inv_id_apply _ _
  change (show Γ(M, h ''ᵁ ⊤) from (h.appIso ⊤).inv ((Spec A).presheaf.map
      (⊤ : (Spec A).Opens).leTop.op ((Scheme.ΓSpecIso A).inv
        ((Scheme.ΓSpecIso A).hom ((h.appIso ⊤).hom r)))) • (show Γ(M, h ''ᵁ ⊤) from m)) = _
  rw [e1, e2]

/-- The germ at a chart point of a function restricted to the chart image. -/
lemma stalkMap_germ_appIso_inv' (x : Spec A) (r : Γ(Spec A, ⊤)) :
    h.stalkMap x (Y.presheaf.germ (h ''ᵁ ⊤) (h x) ⟨x, trivial, rfl⟩ ((h.appIso ⊤).inv r)) =
      (Spec A).presheaf.germ ⊤ x trivial r := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  change (Spec A).presheaf.germ (h ⁻¹ᵁ h ''ᵁ ⊤) x _
      (((h.appIso ⊤).inv ≫ h.app (h ''ᵁ ⊤)) r) = _
  rw [Scheme.Hom.appIso_inv_app]
  exact (Spec A).presheaf.germ_res_apply (eqToHom (h.preimage_image_eq ⊤)) x (by simp) r

/-- A function on the chart, written through the coordinate ring, acts on the actual stalk
of an associated sheaf through the localization map. -/
lemma germ_smul_toStalk (N : ModuleCat.{u} A) (x : Spec A) (a : A) (z : N) :
    (Spec A).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso A).inv a) •
        (show stalk (tilde N) x from (tilde.toStalk N x).hom z) =
      (tilde.toStalk N x).hom (a • z) := by
  rw [map_smul, ← (Spec A).presheaf.germ_res_apply
    (homOfLE (le_top : (⊤ : (Spec A).Opens) ≤ ⊤)) x trivial]
  rfl

lemma sum_smul_single {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    ∑ k, v k • Pi.single k (1 : R) = v := by
  ext i
  simp [Pi.single_apply]

instance {R : Type u} [CommRing R] {n m : ℕ} (ρ : Fin m → Fin n → R) :
    Module.FinitePresentation R ((Fin n → R) ⧸ Submodule.span R (Set.range ρ)) :=
  Module.finitePresentation_of_surjective _ (Submodule.mkQ_surjective _)
    (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range ρ))

/-- The module with generators indexed by `Fin n` and relations `ρ`, mapped to global
sections by sending the generators to `s`. -/
def presentedMap (F : (Spec A).Modules) {n m : ℕ} (s : Fin n → moduleSpecΓFunctor.obj F)
    (ρ : Fin m → Fin n → A) (hρs : ∀ j, ∑ k, ρ j k • s k = 0) :
    ModuleCat.of A ((Fin n → A) ⧸ Submodule.span A (Set.range ρ)) ⟶ moduleSpecΓFunctor.obj F :=
  ModuleCat.ofHom (Y := moduleSpecΓFunctor.obj F) ((Submodule.span A (Set.range ρ)).liftQ
    (@Fintype.linearCombination (Fin n) (moduleSpecΓFunctor.obj F) A _ _ _
      (moduleSpecΓFunctor.obj F).isModule s) (by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hρs j))

lemma presentedMap_single (F : (Spec A).Modules) {n m : ℕ}
    (s : Fin n → moduleSpecΓFunctor.obj F) (ρ : Fin m → Fin n → A)
    (hρs : ∀ j, ∑ k, ρ j k • s k = 0) (k : Fin n) :
    (presentedMap F s ρ hρs).hom ((Submodule.span A (Set.range ρ)).mkQ (Pi.single k 1)) =
      s k := by
  rw [presentedMap, ModuleCat.hom_ofHom, Submodule.mkQ_apply, Submodule.liftQ_apply,
    Fintype.linearCombination_apply_single, one_smul]

/-- Generators of a module give generators of every stalk of the associated sheaf over the
local ring. -/
lemma span_range_toStalk_eq_top (N : ModuleCat.{u} A) (a₀ : Spec A) {ι : Type*} (v : ι → N)
    (hv : Submodule.span A (Set.range v) = ⊤) :
    Submodule.span ((Spec A).presheaf.stalk a₀)
      (Set.range fun i => (show stalk (tilde N) a₀ from (tilde.toStalk N a₀).hom (v i))) = ⊤ := by
  let : Algebra A ((Spec A).presheaf.stalk a₀) :=
    inferInstanceAs (Algebra A ((structurePresheafInCommRingCat A).stalk a₀))
  let : IsLocalization a₀.asIdeal.primeCompl ((Spec A).presheaf.stalk a₀) :=
    inferInstanceAs (IsLocalization a₀.asIdeal.primeCompl
      ((structurePresheafInCommRingCat A).stalk a₀))
  let : IsScalarTower A ((Spec A).presheaf.stalk a₀) (stalk (tilde N) a₀) :=
    inferInstanceAs (IsScalarTower A ((structurePresheafInCommRingCat A).stalk a₀)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf A N).presheaf a₀))
  have := span_eq_top_of_isLocalizedModule ((Spec A).presheaf.stalk a₀)
    a₀.asIdeal.primeCompl (tilde.toStalk N a₀).hom hv
  rw [← Set.range_comp] at this
  exact this

/-- At a chart point, the comparison map from the presented module to the restriction is a
stalk isomorphism when the generators and relations, transported to the image point,
present the stalk there. -/
lemma mem_isoLocus_chart (M : Y.Modules) (a₀ : Spec A) {n m : ℕ}
    (s : Fin n → moduleSpecΓFunctor.obj (M.restrict h)) (ρ : Fin m → Fin n → A)
    (hρs : ∀ j, ∑ k, ρ j k • s k = 0) (κ : Fin m → Fin n → Y.presheaf.stalk (h a₀))
    (hκ : ∀ j k, h.stalkMap a₀ (κ j k) =
      (Spec A).presheaf.germ ⊤ a₀ trivial ((Scheme.ΓSpecIso A).inv (ρ j k)))
    (hspan : Submodule.span (Y.presheaf.stalk (h a₀)) (Set.range fun k =>
      M.presheaf.germ (h ''ᵁ ⊤) (h a₀) ⟨a₀, trivial, rfl⟩ (s k)) = ⊤)
    (hker : ∀ c : Fin n → Y.presheaf.stalk (h a₀),
      ∑ k, c k • M.presheaf.germ (h ''ᵁ ⊤) (h a₀) ⟨a₀, trivial, rfl⟩ (s k) = 0 →
        c ∈ Submodule.span (Y.presheaf.stalk (h a₀)) (Set.range κ)) :
    a₀ ∈ isoLocus (tilde.map (presentedMap (M.restrict h) s ρ hρs) ≫
      (M.restrict h).fromTildeΓ) := by
  set K := Submodule.span A (Set.range ρ)
  set N := ModuleCat.of A ((Fin n → A) ⧸ K)
  set c := tilde.map (presentedMap (M.restrict h) s ρ hρs) ≫ (M.restrict h).fromTildeΓ
  let x : Fin n → stalk (tilde N) a₀ := fun k => (tilde.toStalk N a₀).hom (K.mkQ (Pi.single k 1))
  -- The images of the generators span the stalk over the chart local ring.
  have hv : Submodule.span A (Set.range fun k : Fin n => K.mkQ (Pi.single k (1 : A))) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨v, rfl⟩ := K.mkQ_surjective z
    rw [← sum_smul_single v, map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hx' : Submodule.span ((Spec A).presheaf.stalk a₀) (Set.range x) = ⊤ :=
    span_range_toStalk_eq_top N a₀ _ hv
  let := relativeStalkModule h (tilde N) a₀
  let := relativeStalkModule h (M.restrict h) a₀
  let e := restrictStalkLinearEquiv h M a₀
  let ℓ := e.toLinearMap ∘ₗ relativeStalkMap h c a₀
  have hx : Submodule.span (Y.presheaf.stalk (h a₀)) (Set.range x) = ⊤ :=
    Langlands.CommutativeAlgebra.span_eq_top_of_surjective (h.stalkMap a₀).hom
      (ConcreteCategory.bijective_of_isIso (h.stalkMap a₀)).2 (fun _ _ => rfl) hx'
  have hρ : ∀ j, ∑ k, κ j k • x k = 0 := by
    intro j
    have h1 : ∀ k, κ j k • x k = (tilde.toStalk N a₀).hom (ρ j k • K.mkQ (Pi.single k 1)) := by
      intro k
      rw [← germ_smul_toStalk N a₀ (ρ j k), ← hκ j k]
      rfl
    have h2 : ∑ k, ρ j k • K.mkQ (Pi.single k (1 : A)) = 0 := by
      simp_rw [← LinearMap.map_smul, ← map_sum, sum_smul_single]
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨j, rfl⟩
    rw [Finset.sum_congr rfl fun k _ => h1 k, ← map_sum, h2, map_zero]
  have hℓx : ∀ k, ℓ (x k) = M.presheaf.germ (h ''ᵁ ⊤) (h a₀) ⟨a₀, trivial, rfl⟩ (s k) := by
    intro k
    change e (stalkMap (tilde.map (presentedMap (M.restrict h) s ρ hρs) ≫
      (M.restrict h).fromTildeΓ) a₀ ((tilde.toStalk N a₀).hom (K.mkQ (Pi.single k 1)))) = _
    rw [stalkMap_comp, LinearMap.comp_apply, stalkMap_tilde_map_toStalk, presentedMap_single]
    exact (congrArg e (stalkMap_fromTildeΓ_toStalk (M.restrict h) a₀ (s k))).trans
      (restrictStalkLinearEquiv_germ ..)
  have hℓ : Submodule.span (Y.presheaf.stalk (h a₀)) (Set.range (ℓ ∘ x)) = ⊤ := by
    rw [show ℓ ∘ x = _ from funext hℓx]
    exact hspan
  have hker' : ∀ c' : Fin n → Y.presheaf.stalk (h a₀), ∑ k, c' k • ℓ (x k) = 0 →
      c' ∈ Submodule.span (Y.presheaf.stalk (h a₀)) (Set.range κ) := fun c' hc =>
    hker c' (by simpa only [hℓx] using hc)
  have hbij := Langlands.CommutativeAlgebra.bijective_of_presentation x hx κ hρ ℓ hℓ hker'
  rw [LinearMap.coe_comp, LinearEquiv.coe_coe] at hbij
  exact (Function.Bijective.of_comp_iff' e.bijective _).mp hbij

end Chart

/-- The stalks of a module sheaf whose pullback along a flat surjection is locally
finitely presented are finitely presented. -/
lemma finitePresentation_stalk_of_pullback (p : X ⟶ Y) [Flat p] [Surjective p]
    (M : Y.Modules) [((Scheme.Modules.pullback p).obj M).IsFinitePresentation] (y : Y) :
    Module.FinitePresentation (Y.presheaf.stalk y) (stalk M y) := by
  obtain ⟨x, rfl⟩ := p.surjective y
  let : Algebra (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  have : Module.FaithfullyFlat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    faithfullyFlat_stalkMap p x
  have : Module.FinitePresentation (X.presheaf.stalk x)
      (stalk ((Scheme.Modules.pullback p).obj M) x) :=
    finitePresentation_stalk _ x
  have : Module.FinitePresentation (X.presheaf.stalk x)
      (X.presheaf.stalk x ⊗[Y.presheaf.stalk (p x)] stalk M (p x)) :=
    Module.FinitePresentation.of_equiv (StalkPullback.pullbackStalkTensorEquiv p x M)
  exact Langlands.CommutativeAlgebra.finitePresentation_of_finitePresentation_tensorProduct
    (X.presheaf.stalk x)

/-- A module sheaf whose pullback along a flat, locally finitely presented surjection is
locally finitely presented has a finite presentation on an open neighbourhood of every
point. -/
lemma exists_presentation_restrict_of_pullback (p : X ⟶ Y) [Flat p]
    [LocallyOfFinitePresentation p] [Surjective p] (M : Y.Modules)
    [((Scheme.Modules.pullback p).obj M).IsFinitePresentation] (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ P : (M.restrict U.ι).Presentation, P.IsFinite := by
  have hfp := finitePresentation_stalk_of_pullback p M y
  -- Generators and relations of the stalk.
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := Y.presheaf.stalk y) (M := stalk M y)
  let π := Fintype.linearCombination (Y.presheaf.stalk y) b
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hb]
  obtain ⟨m, κ, hκ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.FinitePresentation.fg_ker π hπ)
  -- Lift them to sections over a common neighbourhood on which the relations hold.
  obtain ⟨U₁, hy₁, s, hs⟩ := exists_forall_germ_eq M y b
  obtain ⟨U₂, hy₂, r, hr⟩ :=
    exists_forall_germ_eq_ring y (fun jk : Fin m × Fin n => κ jk.1 jk.2)
  let V := U₁ ⊓ U₂
  have hyV : y ∈ V := ⟨hy₁, hy₂⟩
  let sV : Fin n → Γ(M, V) := fun k => M.presheaf.map (homOfLE inf_le_left).op (s k)
  let rV : Fin m → Fin n → Γ(Y, V) := fun j k =>
    Y.presheaf.map (homOfLE inf_le_right).op (r (j, k))
  have hsV : ∀ k, M.presheaf.germ V y hyV (sV k) = b k := fun k => by
    rw [TopCat.Presheaf.germ_res_apply]; exact hs k
  have hrV : ∀ j k, Y.presheaf.germ V y hyV (rV j k) = κ j k := fun j k => by
    rw [TopCat.Presheaf.germ_res_apply]; exact hr (j, k)
  let rel : Fin m → Γ(M, V) := fun j => ∑ k, rV j k • sV k
  have hrel : ∀ j, M.presheaf.germ V y hyV (rel j) = 0 := by
    intro j
    have hmem : κ j ∈ LinearMap.ker π := hκ ▸ Submodule.subset_span ⟨j, rfl⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hmem
    simp only [rel, map_sum]
    refine (Finset.sum_congr rfl fun k _ => ?_).trans hmem
    rw [← hsV k, ← hrV j k]
    exact PresheafOfModules.germ_smul M.val y V hyV (rV j k) (sV k)
  obtain ⟨W, hWV, hyW, hW⟩ := exists_le_forall_map_eq_zero M hyV rel hrel
  -- An affine chart inside that neighbourhood.
  obtain ⟨A, h, _, ⟨a₀, rfl⟩, hrange⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := W) hyW
  have hle : h ''ᵁ ⊤ ≤ W := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hrange
  have hleV : h ''ᵁ ⊤ ≤ V := hle.trans hWV
  let s' : Fin n → moduleSpecΓFunctor.obj (M.restrict h) := fun k =>
    M.presheaf.map (homOfLE hleV).op (sV k)
  let t : Fin m → Fin n → Γ(Spec A, ⊤) := fun j k =>
    (h.appIso ⊤).hom (Y.presheaf.map (homOfLE hleV).op (rV j k))
  let ρ : Fin m → Fin n → A := fun j k => (Scheme.ΓSpecIso A).hom (t j k)
  have hρs : ∀ j, ∑ k, ρ j k • s' k = 0 := by
    intro j
    have h1 : ∀ k, ρ j k • s' k = M.presheaf.map (homOfLE hleV).op (rV j k • sV k) := by
      intro k
      rw [Scheme.Modules.map_smul]
      exact restrict_smul_Spec h M _ _
    rw [Finset.sum_congr rfl fun k _ => h1 k]
    change (∑ k, M.presheaf.map (homOfLE hleV).op (rV j k • sV k) : Γ(M, h ''ᵁ ⊤)) = 0
    rw [← map_sum]
    change M.presheaf.map (homOfLE hleV).op (rel j) = 0
    rw [show homOfLE hleV = homOfLE hle ≫ homOfLE hWV from rfl, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, hW j, map_zero]
  have hgerm : ∀ k, M.presheaf.germ (h ''ᵁ ⊤) (h a₀) ⟨a₀, trivial, rfl⟩ (s' k) = b k := by
    intro k
    rw [TopCat.Presheaf.germ_res_apply]
    exact hsV k
  set c := tilde.map (presentedMap (M.restrict h) s' ρ hρs) ≫ (M.restrict h).fromTildeΓ
  have ha₀ : a₀ ∈ isoLocus c := by
    refine mem_isoLocus_chart h M a₀ s' ρ hρs κ (fun j k => ?_) ?_ ?_
    · rw [show (Scheme.ΓSpecIso A).inv (ρ j k) = t j k from Iso.hom_inv_id_apply _ _,
        ← hrV j k, ← Y.presheaf.germ_res_apply (homOfLE hleV) (h a₀) ⟨a₀, trivial, rfl⟩,
        show Y.presheaf.map (homOfLE hleV).op (rV j k) = (h.appIso ⊤).inv (t j k) from
          (Iso.hom_inv_id_apply _ _).symm]
      exact stalkMap_germ_appIso_inv' h a₀ (t j k)
    · rw [show (fun k => M.presheaf.germ (h ''ᵁ ⊤) (h a₀) ⟨a₀, trivial, rfl⟩ (s' k)) = b from
        funext hgerm]
      exact hb
    · intro c' hc
      rw [hκ, LinearMap.mem_ker, Fintype.linearCombination_apply]
      simpa only [hgerm] using hc
  -- The stalk-isomorphism locus is open, by descent along the base change of `p`.
  obtain ⟨PN, hPN⟩ := exists_presentation_tilde
    (ModuleCat.of A ((Fin n → A) ⧸ Submodule.span A (Set.range ρ)))
  let p' := pullback.snd p h
  have : ((Scheme.Modules.pullback p').obj
      (tilde (ModuleCat.of A ((Fin n → A) ⧸ Submodule.span A (Set.range ρ))))).IsFinitePresentation :=
    isFinitePresentation_of_presentation (presentationPullback p' PN)
  have : ((Scheme.Modules.pullback p').obj (M.restrict h)).IsFinitePresentation := by
    let e : (Scheme.Modules.pullback p').obj (M.restrict h) ≅
        (Scheme.Modules.pullback (pullback.fst p h)).obj ((Scheme.Modules.pullback p).obj M) :=
      (Scheme.Modules.pullback p').mapIso ((Scheme.Modules.restrictFunctorIsoPullback h).app M) ≪≫
        (Scheme.Modules.pullbackComp p' h).app M ≪≫
        (Scheme.Modules.pullbackCongr pullback.condition.symm).app M ≪≫
        ((Scheme.Modules.pullbackComp (pullback.fst p h) p).app M).symm
    have := isFinitePresentation_pullback (pullback.fst p h) ((Scheme.Modules.pullback p).obj M)
    exact (SheafOfModules.isFinitePresentation (Limits.pullback p h).ringCatSheaf).prop_of_iso
      e.symm this
  have hopen : IsOpen (isoLocus c) := isOpen_isoLocus_of_pullback p' c
  -- On the open locus the comparison map is an isomorphism, giving the presentation.
  let W' : (Spec A).Opens := ⟨isoLocus c, hopen⟩
  have : IsIso ((Scheme.Modules.restrictFunctor W'.ι).map c) := by
    rw [isIso_iff_forall_mem_isoLocus]
    intro w
    rw [mem_isoLocus_restrict_iff]
    exact w.2
  let P₃ : (M.restrict (W'.ι ≫ h)).Presentation :=
    ((Scheme.Modules.presentationRestrict W'.ι PN).ofIsIso
      ((Scheme.Modules.restrictFunctor W'.ι).map c)).ofIsIso
      ((Scheme.Modules.restrictFunctorComp W'.ι h).app M).inv
  have : P₃.IsFinite := by
    dsimp [P₃, Scheme.Modules.presentationRestrict]
    infer_instance
  obtain ⟨P', hP'⟩ := exists_presentation_opensRange M (W'.ι ≫ h) P₃
  exact ⟨(W'.ι ≫ h).opensRange, ⟨⟨a₀, ha₀⟩, rfl⟩, P', hP'⟩

/-- **Descent of local finite presentation along fppf coverings.** A module sheaf whose
pullback along a flat, locally finitely presented surjection is locally finitely presented
is itself locally finitely presented. -/
lemma isFinitePresentation_of_pullback_fppf {X Y : Scheme.{u}} (p : X ⟶ Y) [Flat p]
    [LocallyOfFinitePresentation p] [Surjective p] (M : Y.Modules)
    [((Scheme.Modules.pullback p).obj M).IsFinitePresentation] : M.IsFinitePresentation :=
  isFinitePresentation_of_forall_exists_presentation M
    (exists_presentation_restrict_of_pullback p M)

end Langlands.AlgebraicGeometry.Modules
