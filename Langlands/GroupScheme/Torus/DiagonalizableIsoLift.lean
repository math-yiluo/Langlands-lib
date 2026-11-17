import Langlands.GroupScheme.Torus.FreeCharacterCoverTorus
import Langlands.GroupScheme.Descent.DisjointPullbackCoherence

/-! # Lifting isomorphisms of diagonalizable groups to their free covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

open Descent FreeCharacterCover

variable {X Y W : Scheme.{u}}

/-- Every map to `Spec ℤ` is the unique one. -/
theorem toSpecZ_comp (q : Y ⟶ X) : q ≫ Gm.toSpecZ X = Gm.toSpecZ Y :=
  specULiftZIsTerminal.hom_ext _ _

/-! ### Homomorphisms of base changes are determined on an open cover -/

/-- Homomorphisms between base changes agree if they agree after restriction to the members
of an open cover. -/
theorem baseChange_hom_ext_of_opens {S : Scheme.{u}} {f : X ⟶ S} {G H : GroupScheme S}
    (r : ∀ V : X.Opens, (V : Scheme.{u}) ⟶ S) (hr : ∀ V : X.Opens, V.ι ≫ f = r V)
    {φ ψ : (GroupScheme.baseChange f).obj G ⟶ (GroupScheme.baseChange f).obj H}
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      pullHom V.ι (hr V) (hr V) φ = pullHom V.ι (hr V) (hr V) ψ) :
    φ = ψ := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply Scheme.hom_ext_of_forall
    intro y
    obtain ⟨V, hxV, hV⟩ := h (pullback.snd G.X.hom f y)
    let U : Scheme.Opens _ := pullback.snd G.X.hom f ⁻¹ᵁ V
    refine ⟨U, hxV, ?_⟩
    have hrange : Set.range (U.ι ≫ pullback.snd G.X.hom f) ⊆ Set.range V.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let z := IsOpenImmersion.lift V.ι (U.ι ≫ pullback.snd G.X.hom f) hrange
    have hz : z ≫ V.ι = U.ι ≫ pullback.snd G.X.hom f := IsOpenImmersion.lift_fac _ _ _
    have ha : (U.ι ≫ pullback.fst G.X.hom f) ≫ G.X.hom = z ≫ r V := by
      rw [← hr V, ← Category.assoc z, hz]
      simp only [Category.assoc, pullback.condition]
    have hU : pullback.lift (U.ι ≫ pullback.fst G.X.hom f) (z ≫ V.ι)
        (by simp only [Category.assoc, ← hr V] at ha ⊢; exact ha) = U.ι := by
      apply pullback.hom_ext
      · simp
      · simp [hz]
    have key := fun (e : (GroupScheme.baseChange f).obj G ⟶ (GroupScheme.baseChange f).obj H) =>
      pullHom_eval V.ι (hr V) (hr V) e (U.ι ≫ pullback.fst G.X.hom f) z ha
    have hφ := key φ
    have hψ := key ψ
    rw [hU] at hφ hψ
    rw [← hφ, ← hψ, hV]
  · exact (Over.w φ.hom.hom).trans (Over.w ψ.hom.hom).symm

/-! ### Pulling back homomorphisms of diagonalizable groups -/

section Pull

variable {Λ Λ' Λ'' : Type u} [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']

/-- The pullback of a homomorphism `D_X(Λ) ⟶ D_X(Λ')` along `q : Y ⟶ X`, as a homomorphism
`D_Y(Λ) ⟶ D_Y(Λ')`. -/
def dpull (q : Y ⟶ X) (φ : diagonalizable X Λ ⟶ diagonalizable X Λ') :
    diagonalizable Y Λ ⟶ diagonalizable Y Λ' :=
  pullHom q (toSpecZ_comp q) (toSpecZ_comp q) φ

theorem dpull_eq (q : Y ⟶ X) (φ : diagonalizable X Λ ⟶ diagonalizable X Λ') :
    dpull q φ = (diagonalizableBaseChangeIso q Λ).inv ≫ (GroupScheme.baseChange q).map φ ≫
      (diagonalizableBaseChangeIso q Λ').hom :=
  rfl

@[simp] theorem dpull_id (q : Y ⟶ X) : dpull q (𝟙 (diagonalizable X Λ)) = 𝟙 _ :=
  pullHom_id q _ _ _ _

@[simp] theorem dpull_comp (q : Y ⟶ X) (φ : diagonalizable X Λ ⟶ diagonalizable X Λ')
    (ψ : diagonalizable X Λ' ⟶ diagonalizable X Λ'') :
    dpull q (φ ≫ ψ) = dpull q φ ≫ dpull q ψ :=
  pullHom_comp q _ _ _ φ ψ

theorem dpull_dpull (q : Y ⟶ X) (r : W ⟶ Y) (φ : diagonalizable X Λ ⟶ diagonalizable X Λ') :
    dpull r (dpull q φ) = dpull (r ≫ q) φ :=
  pullHom_pullHom q r _ _ _ _ φ

@[simp] theorem dpull_identity (φ : diagonalizable X Λ ⟶ diagonalizable X Λ') :
    dpull (𝟙 X) φ = φ :=
  pullHom_identity φ

theorem dpull_dpull_of_comm {Y' : Scheme.{u}} {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Y'}
    {d : Y' ⟶ X} (h : a ≫ b = c ≫ d) (φ : diagonalizable X Λ ⟶ diagonalizable X Λ') :
    dpull a (dpull b φ) = dpull c (dpull d φ) := by
  rw [dpull_dpull, dpull_dpull, h]

@[simp] theorem dpull_diagonalizableMap (q : Y ⟶ X) (g : Λ' →+ Λ) :
    dpull q (diagonalizableMap X g) = diagonalizableMap Y g :=
  pullHom_map q _ _ (toSpecZ_comp q) _

/-- The pullback of an isomorphism of diagonalizable groups. -/
def dpullIso (q : Y ⟶ X) (u : diagonalizable X Λ ≅ diagonalizable X Λ') :
    diagonalizable Y Λ ≅ diagonalizable Y Λ' :=
  pullIso q (toSpecZ_comp q) (toSpecZ_comp q) u

@[simp] theorem dpullIso_hom (q : Y ⟶ X) (u : diagonalizable X Λ ≅ diagonalizable X Λ') :
    (dpullIso q u).hom = dpull q u.hom :=
  rfl

/-- Homomorphisms of diagonalizable groups agree if they agree on an open cover. -/
theorem dhom_ext {φ ψ : diagonalizable X Λ ⟶ diagonalizable X Λ'}
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ dpull V.ι φ = dpull V.ι ψ) : φ = ψ :=
  baseChange_hom_ext_of_opens (fun V => Gm.toSpecZ V) (fun V => toSpecZ_comp V.ι) h

/-- Isomorphisms of diagonalizable groups agree if they agree on an open cover. -/
theorem diso_ext {u v : diagonalizable X Λ ≅ diagonalizable X Λ'}
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ dpull V.ι u.hom = dpull V.ι v.hom) : u = v :=
  Iso.ext (dhom_ext h)

theorem exists_open_dpull [AddGroup.FG Λ] [AddGroup.FG Λ']
    (u : diagonalizable X Λ ⟶ diagonalizable X Λ') (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ g : Λ' →+ Λ, dpull V.ι u = diagonalizableMap V g := by
  obtain ⟨V, hx, g, h⟩ := exists_opens_baseChange_map_eq u x
  refine ⟨V, hx, g, ?_⟩
  rw [dpull_eq, h]
  simp

theorem dpull_of_le {u : diagonalizable X Λ ⟶ diagonalizable X Λ'} {g : Λ' →+ Λ}
    {V V' : X.Opens} (hle : V' ≤ V) (h : dpull V.ι u = diagonalizableMap V g) :
    dpull V'.ι u = diagonalizableMap V' g := by
  rw [← X.homOfLE_ι hle, ← dpull_dpull, h, dpull_diagonalizableMap]

theorem eq_of_dpull {u : diagonalizable X Λ ⟶ diagonalizable X Λ'} {g g' : Λ' →+ Λ}
    {V : X.Opens} {x : X} (hx : x ∈ V) (h : dpull V.ι u = diagonalizableMap V g)
    (h' : dpull V.ι u = diagonalizableMap V g') : g = g' := by
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  exact diagonalizableMap_injective (h.symm.trans h')

/-- The isomorphism `D_X(g) : D_X(Λ) ≅ D_X(Λ')` induced by `g : Λ' ≃+ Λ`. -/
def diagonalizableIso (X : Scheme.{u}) (g : Λ' ≃+ Λ) :
    diagonalizable X Λ ≅ diagonalizable X Λ' where
  hom := diagonalizableMap X g.toAddMonoidHom
  inv := diagonalizableMap X g.symm.toAddMonoidHom
  hom_inv_id := by
    rw [diagonalizableMap_comp]
    have : g.toAddMonoidHom.comp g.symm.toAddMonoidHom = AddMonoidHom.id Λ :=
      AddMonoidHom.ext fun x => g.apply_symm_apply x
    rw [this, diagonalizableMap_id]
  inv_hom_id := by
    rw [diagonalizableMap_comp]
    have : g.symm.toAddMonoidHom.comp g.toAddMonoidHom = AddMonoidHom.id Λ' :=
      AddMonoidHom.ext fun x => g.symm_apply_apply x
    rw [this, diagonalizableMap_id]

@[simp] theorem diagonalizableIso_hom (X : Scheme.{u}) (g : Λ' ≃+ Λ) :
    (diagonalizableIso X g).hom = diagonalizableMap X g.toAddMonoidHom :=
  rfl

end Pull

/-! ### The loci where a homomorphism is given by a fixed character map -/

section Locus

variable {Λ Λ' Λ'' : Type u} [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']

/-- The union of the opens on which `u` restricts to `D(g)`. -/
def locus (u : diagonalizable X Λ ⟶ diagonalizable X Λ') (g : Λ' ≃+ Λ) : X.Opens :=
  sSup {V : X.Opens | dpull V.ι u = diagonalizableMap V g.toAddMonoidHom}

theorem le_locus {u : diagonalizable X Λ ⟶ diagonalizable X Λ'} {g : Λ' ≃+ Λ} {V : X.Opens}
    (h : dpull V.ι u = diagonalizableMap V g.toAddMonoidHom) : V ≤ locus u g :=
  le_sSup h

theorem mem_locus {u : diagonalizable X Λ ⟶ diagonalizable X Λ'} {g : Λ' ≃+ Λ} {x : X} :
    x ∈ locus u g ↔
      ∃ V : X.Opens, x ∈ V ∧ dpull V.ι u = diagonalizableMap V g.toAddMonoidHom := by
  rw [locus, TopologicalSpace.Opens.mem_sSup]
  constructor
  · rintro ⟨V, hV, hx⟩
    exact ⟨V, hx, hV⟩
  · rintro ⟨V, hx, hV⟩
    exact ⟨V, hV, hx⟩

theorem locus_disjoint (u : diagonalizable X Λ ⟶ diagonalizable X Λ') {g g' : Λ' ≃+ Λ}
    (hgg : g ≠ g') : Disjoint (locus u g) (locus u g') := by
  rw [disjoint_iff]
  ext x
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
    TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hx'
  obtain ⟨V, hxV, hV⟩ := mem_locus.mp hx
  obtain ⟨V', hxV', hV'⟩ := mem_locus.mp hx'
  apply hgg
  apply AddEquiv.toAddMonoidHom_injective
  exact eq_of_dpull (show x ∈ V ⊓ V' from ⟨hxV, hxV'⟩) (dpull_of_le inf_le_left hV)
    (dpull_of_le inf_le_right hV')

theorem locus_cover [AddGroup.FG Λ] [AddGroup.FG Λ']
    (u : diagonalizable X Λ ≅ diagonalizable X Λ') (x : X) :
    ∃ g : Λ' ≃+ Λ, x ∈ locus u.hom g := by
  obtain ⟨V, hxV, g, hV⟩ := exists_open_dpull u.hom x
  obtain ⟨V', hxV', g', hV'⟩ := exists_open_dpull u.inv x
  have hW : dpull (V ⊓ V').ι u.hom = diagonalizableMap _ g := dpull_of_le inf_le_left hV
  have hW' : dpull (V ⊓ V').ι u.inv = diagonalizableMap _ g' := dpull_of_le inf_le_right hV'
  have hxW : x ∈ V ⊓ V' := ⟨hxV, hxV'⟩
  have h1 : g.comp g' = AddMonoidHom.id Λ := by
    refine eq_of_dpull (u := 𝟙 (diagonalizable X Λ)) hxW ?_ ?_
    · rw [← diagonalizableMap_comp, ← hW, ← hW', ← dpull_comp, u.hom_inv_id]
    · rw [dpull_id, diagonalizableMap_id]
  have h2 : g'.comp g = AddMonoidHom.id Λ' := by
    refine eq_of_dpull (u := 𝟙 (diagonalizable X Λ')) hxW ?_ ?_
    · rw [← diagonalizableMap_comp, ← hW, ← hW', ← dpull_comp, u.inv_hom_id]
    · rw [dpull_id, diagonalizableMap_id]
  exact ⟨AddMonoidHom.toAddEquiv g g' h2 h1, mem_locus.mpr ⟨_, hxW, hW⟩⟩

theorem exists_open_dpull_iso [AddGroup.FG Λ] [AddGroup.FG Λ']
    (u : diagonalizable X Λ ≅ diagonalizable X Λ') (x : X) :
    ∃ g : Λ' ≃+ Λ, ∃ V : X.Opens, x ∈ V ∧
      dpull V.ι u.hom = diagonalizableMap V g.toAddMonoidHom := by
  obtain ⟨g, hg⟩ := locus_cover u x
  exact ⟨g, mem_locus.mp hg⟩

instance locus_isIso [AddGroup.FG Λ] [AddGroup.FG Λ']
    (u : diagonalizable X Λ ≅ diagonalizable X Λ') :
    IsIso (Sigma.desc fun g : Λ' ≃+ Λ => (locus u.hom g).ι) := by
  have hcol := nonempty_isColimit_cofanMk_of (fun g : Λ' ≃+ Λ => (locus u.hom g).ι) ?_ ?_
  · exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hcol
  · rw [eq_top_iff]
    intro x _
    obtain ⟨g, hg⟩ := locus_cover u x
    simp only [Scheme.Opens.opensRange_ι]
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨g, hg⟩
  · intro g g' hgg
    simp only [Function.onFun, Scheme.Opens.opensRange_ι]
    exact locus_disjoint _ hgg

end Locus

/-! ### The lifted isomorphism of free covers -/

section Lift

variable {Λ Λ' Λ'' : Type u} [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']
  [AddGroup.FG Λ] [AddGroup.FG Λ'] [AddGroup.FG Λ'']

/-- The isomorphism `D_X(F(Λ)) ≅ D_X(F(Λ'))` of free covers lifting `u : D_X(Λ) ≅ D_X(Λ')`:
on the locus where `u = D(g)` it is `D(F(g))`. -/
def liftIso (u : diagonalizable X Λ ≅ diagonalizable X Λ') :
    diagonalizable X (Cover Λ) ≅ diagonalizable X (Cover Λ') :=
  DisjointComponents.pullbackIsoAlong (fun g : Λ' ≃+ Λ => (locus u.hom g).ι)
    (fun _ => toSpecZ_comp _) (fun _ => toSpecZ_comp _)
    (fun g => diagonalizableIso _ (coverEquiv g))

/-- On any open on which `u = D(g)`, the lift is `D(F(g))`. -/
theorem dpull_liftIso (u : diagonalizable X Λ ≅ diagonalizable X Λ') {g : Λ' ≃+ Λ}
    {V : X.Opens} (hV : dpull V.ι u.hom = diagonalizableMap V g.toAddMonoidHom) :
    dpull V.ι (liftIso u).hom = diagonalizableMap V (coverEquiv g).toAddMonoidHom := by
  have hle := le_locus hV
  have h := congrArg Iso.hom
    (DisjointComponents.pullIso_pullbackIsoAlong_factor
      (fun g : Λ' ≃+ Λ => (locus u.hom g).ι)
      (fun _ => toSpecZ_comp _) (fun _ => toSpecZ_comp _)
      (fun g => diagonalizableIso _ (coverEquiv g)) g (X.homOfLE hle) (X.homOfLE_ι hle)
      (toSpecZ_comp V.ι) (toSpecZ_comp V.ι))
  rw [pullIso_hom, pullIso_hom] at h
  exact h.trans (dpull_diagonalizableMap _ _)

/-- The lift is compatible with the projections `D(Λ) ⟶ D(F(Λ))`. -/
theorem liftIso_comm (u : diagonalizable X Λ ≅ diagonalizable X Λ') :
    u.hom ≫ diagonalizableMap X (proj Λ') =
      diagonalizableMap X (proj Λ) ≫ (liftIso u).hom := by
  apply dhom_ext
  intro x
  obtain ⟨g, V, hxV, hV⟩ := exists_open_dpull_iso u x
  refine ⟨V, hxV, ?_⟩
  rw [dpull_comp, dpull_comp, hV, dpull_liftIso u hV, dpull_diagonalizableMap,
    dpull_diagonalizableMap, diagonalizableMap_comp, diagonalizableMap_comp]
  exact congrArg _ (proj_comp_coverEquiv g).symm

/-- The lift commutes with pullback. -/
theorem dpull_liftIso_hom (q : Y ⟶ X) (u : diagonalizable X Λ ≅ diagonalizable X Λ') :
    dpull q (liftIso u).hom = (liftIso (dpullIso q u)).hom := by
  apply dhom_ext
  intro y
  obtain ⟨g, V, hxV, hV⟩ := exists_open_dpull_iso u (q y)
  refine ⟨q ⁻¹ᵁ V, hxV, ?_⟩
  have hc : (q ⁻¹ᵁ V).ι ≫ q = q.resLE V (q ⁻¹ᵁ V) le_rfl ≫ V.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have hW : dpull (q ⁻¹ᵁ V).ι (dpullIso q u).hom =
      diagonalizableMap _ g.toAddMonoidHom := by
    rw [dpullIso_hom, dpull_dpull_of_comm hc, hV, dpull_diagonalizableMap]
  rw [dpull_liftIso _ hW, dpull_dpull_of_comm hc, dpull_liftIso u hV, dpull_diagonalizableMap]

/-- The lift of a pullback is the pullback of the lift. -/
theorem liftIso_dpullIso (q : Y ⟶ X) (u : diagonalizable X Λ ≅ diagonalizable X Λ') :
    liftIso (dpullIso q u) = dpullIso q (liftIso u) :=
  Iso.ext (dpull_liftIso_hom q u).symm

/-- The lift respects composition. -/
theorem liftIso_trans (u : diagonalizable X Λ ≅ diagonalizable X Λ')
    (v : diagonalizable X Λ' ≅ diagonalizable X Λ'') :
    liftIso (u ≪≫ v) = liftIso u ≪≫ liftIso v := by
  apply diso_ext
  intro x
  obtain ⟨g, V, hxV, hV⟩ := exists_open_dpull_iso u x
  obtain ⟨h, V', hxV', hV'⟩ := exists_open_dpull_iso v x
  refine ⟨V ⊓ V', ⟨hxV, hxV'⟩, ?_⟩
  have hW := dpull_of_le (V' := V ⊓ V') inf_le_left hV
  have hW' := dpull_of_le (V' := V ⊓ V') inf_le_right hV'
  have hc : dpull (V ⊓ V').ι (u ≪≫ v).hom =
      diagonalizableMap _ (h.trans g).toAddMonoidHom := by
    rw [Iso.trans_hom, dpull_comp, hW, hW', diagonalizableMap_comp]
    rfl
  rw [dpull_liftIso _ hc, Iso.trans_hom, dpull_comp, dpull_liftIso u hW, dpull_liftIso v hW',
    diagonalizableMap_comp, coverEquiv_trans]
  rfl

/-- The lift of the identity is the identity. -/
theorem liftIso_refl : liftIso (Iso.refl (diagonalizable X Λ)) = Iso.refl _ := by
  apply diso_ext
  intro x
  refine ⟨⊤, trivial, ?_⟩
  have hc : dpull (⊤ : X.Opens).ι (Iso.refl (diagonalizable X Λ)).hom =
      diagonalizableMap _ (AddEquiv.refl Λ).toAddMonoidHom := by
    rw [Iso.refl_hom, dpull_id]
    exact (diagonalizableMap_id _).symm
  rw [dpull_liftIso _ hc, coverEquiv_refl, Iso.refl_hom, dpull_id]
  exact diagonalizableMap_id _

/-- The lift of `D(g)` is `D(F(g))`. -/
theorem liftIso_diagonalizableIso (g : Λ' ≃+ Λ) :
    liftIso (diagonalizableIso X g) = diagonalizableIso X (coverEquiv g) := by
  apply diso_ext
  intro x
  refine ⟨⊤, trivial, ?_⟩
  have hc : dpull (⊤ : X.Opens).ι (diagonalizableIso X g).hom =
      diagonalizableMap _ g.toAddMonoidHom := by
    rw [diagonalizableIso_hom, dpull_diagonalizableMap]
  rw [dpull_liftIso _ hc, diagonalizableIso_hom, dpull_diagonalizableMap]

end Lift

end Langlands.GroupScheme.RelativeMultiplicativeType
