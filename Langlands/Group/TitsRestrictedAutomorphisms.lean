import Langlands.Group.TitsRestrictedPolysimplicial
import Langlands.Group.TitsBorelChambers
import Langlands.Geometry.Building.PolysimplicialCoordinateFibers

/-! # Automorphisms permute the components of the restricted building -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

namespace TitsSystem

section MapEquiv

variable {G : Type*} [Group G]

theorem map_conjugateSubgroup (φ : G ≃* G) (g : G) (L : Subgroup G) :
    (conjugateSubgroup g L).map φ.toMonoidHom =
      conjugateSubgroup (φ g) (L.map φ.toMonoidHom) := by
  simp only [conjugateSubgroup, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem map_symm_map (φ : G ≃* G) (L : Subgroup G) :
    (L.map φ.toMonoidHom).map φ.symm.toMonoidHom = L := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨φ x, ⟨x, hx, rfl⟩, by simp⟩

theorem map_map_symm (φ : G ≃* G) (L : Subgroup G) :
    (L.map φ.symm.toMonoidHom).map φ.toMonoidHom = L := by
  simpa using map_symm_map φ.symm L

theorem map_le_map_iff_equiv (φ : G ≃* G) {L M : Subgroup G} :
    L.map φ.toMonoidHom ≤ M.map φ.toMonoidHom ↔ L ≤ M := by
  refine ⟨fun hLM => ?_, Subgroup.map_mono⟩
  have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hLM
  rwa [map_symm_map, map_symm_map] at this

end MapEquiv

end TitsSystem

namespace IsTitsSystem

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}
  (h : IsTitsSystem B N π S)
include h

/-! ### Admissible types and Borel subgroups -/

theorem standardParabolicSubgroup_self : h.standardParabolicSubgroup (subset_refl S) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨w, hw⟩ := h.exists_mem_cell g
  exact ⟨w, h.closure_eq ▸ Subgroup.mem_top w, hw⟩

/-- A conjugate of a standard parabolic subgroup is admissible exactly when
its type is admissible. -/
theorem isAdmissibleParabolic_conjugate_iff {X : Set W} (hX : X ⊆ S) (g : G) :
    IsAdmissibleParabolic B π S (conjugateSubgroup g (h.standardParabolicSubgroup hX)) ↔
      IsAdmissibleType S X := by
  refine ⟨fun hP => ?_, fun hXa => h.isAdmissibleParabolic_conjugate_standard hXa g⟩
  obtain ⟨k, Y, hY, he⟩ := h.exists_eq_conjugate_of_isAdmissibleParabolic hP
  rwa [h.eq_of_conjugateSubgroup_eq hX hY.1 g k he]

theorem isAdmissibleParabolic_borel : IsAdmissibleParabolic B π S B := by
  simpa using h.isAdmissibleParabolic_conjugate_borel 1

omit h in
/-- Components are the minimal nonadmissible types. -/
theorem not_isAdmissibleType_componentSet (c : Component S) :
    ¬ IsAdmissibleType S (componentSet c) := fun hc => by
  obtain ⟨t, ht, htc⟩ := (isAdmissibleType_iff.mp hc).2 c
  exact htc ht

omit h in
theorem exists_componentSet_subset_of_not_isAdmissibleType {Y : Set W} (hY : Y ⊆ S)
    (hYa : ¬ IsAdmissibleType S Y) : ∃ d : Component S, componentSet d ⊆ Y := by
  by_contra hne
  refine hYa (isAdmissibleType_iff.mpr ⟨hY, fun d => ?_⟩)
  obtain ⟨t, ht, htY⟩ := Set.not_subset.mp (fun hsub => hne ⟨d, hsub⟩)
  exact ⟨t, ht, htY⟩

section TypeCorr

variable (φ : G ≃* G)

/-! ### The type correspondence of an automorphism fixing a Borel class -/

/-- `φ` sends `G_X` to `a G_Y a⁻¹`. -/
def TypeCorr (a : G) (X Y : Set W) : Prop :=
  ∃ (hX : X ⊆ S) (hY : Y ⊆ S), (h.standardParabolicSubgroup hX).map φ.toMonoidHom =
    conjugateSubgroup a (h.standardParabolicSubgroup hY)

variable {φ} {a : G} (ha : B.map φ.toMonoidHom = conjugateSubgroup a B)
include ha

theorem exists_typeCorr_left {X : Set W} (hX : X ⊆ S) : ∃ Y, h.TypeCorr φ a X Y := by
  let H := conjugateSubgroup a⁻¹ ((h.standardParabolicSubgroup hX).map φ.toMonoidHom)
  have hBH : B ≤ H := by
    have h₁ := conjugateSubgroup_mono a⁻¹ (Subgroup.map_mono (f := φ.toMonoidHom)
      (h.le_of_coe_eq rfl : B ≤ h.standardParabolicSubgroup hX))
    rwa [ha, conjugateSubgroup_inv_cancel] at h₁
  obtain ⟨Y, hY, hHY⟩ := h.exists_eq_standardParabolic H hBH
  have hHY' : H = h.standardParabolicSubgroup hY := SetLike.coe_injective hHY
  refine ⟨Y, hX, hY, ?_⟩
  rw [← hHY']
  simp only [H, ← conjugateSubgroup_mul, mul_inv_cancel, conjugateSubgroup_one]

theorem exists_typeCorr_right {Y : Set W} (hY : Y ⊆ S) : ∃ X, h.TypeCorr φ a X Y := by
  let H := (conjugateSubgroup a (h.standardParabolicSubgroup hY)).map φ.symm.toMonoidHom
  have hBH : B ≤ H := by
    have h₁ := Subgroup.map_mono (f := φ.symm.toMonoidHom) (conjugateSubgroup_mono a
      (h.le_of_coe_eq rfl : B ≤ h.standardParabolicSubgroup hY))
    rwa [← ha, map_symm_map] at h₁
  obtain ⟨X, hX, hHX⟩ := h.exists_eq_standardParabolic H hBH
  have hHX' : H = h.standardParabolicSubgroup hX := SetLike.coe_injective hHX
  refine ⟨X, hX, hY, ?_⟩
  rw [← hHX', map_map_symm]

omit ha in
theorem typeCorr_subset_iff {X X' Y Y' : Set W} (hc : h.TypeCorr φ a X Y)
    (hc' : h.TypeCorr φ a X' Y') : X ⊆ X' ↔ Y ⊆ Y' := by
  obtain ⟨hX, hY, he⟩ := hc
  obtain ⟨hX', hY', he'⟩ := hc'
  rw [← h.standardParabolicSubgroup_le_iff hX hX', ← map_le_map_iff_equiv φ, he, he',
    conjugateSubgroup_le_conjugateSubgroup_iff, h.standardParabolicSubgroup_le_iff]

omit ha in
theorem typeCorr_right_unique {X Y Y' : Set W} (hc : h.TypeCorr φ a X Y)
    (hc' : h.TypeCorr φ a X Y') : Y = Y' :=
  subset_antisymm ((h.typeCorr_subset_iff hc hc').mp subset_rfl)
    ((h.typeCorr_subset_iff hc' hc).mp subset_rfl)

omit ha in
theorem typeCorr_left_unique {X X' Y : Set W} (hc : h.TypeCorr φ a X Y)
    (hc' : h.TypeCorr φ a X' Y) : X = X' :=
  subset_antisymm ((h.typeCorr_subset_iff hc hc').mpr subset_rfl)
    ((h.typeCorr_subset_iff hc' hc).mpr subset_rfl)

omit ha in
theorem typeCorr_self : h.TypeCorr φ a S S := by
  refine ⟨subset_refl S, subset_refl S, ?_⟩
  rw [h.standardParabolicSubgroup_self, Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective,
    conjugateSubgroup_eq_self (Subgroup.mem_top a)]

variable (hφ : ∀ P : Subgroup G,
  IsAdmissibleParabolic B π S (P.map φ.toMonoidHom) ↔ IsAdmissibleParabolic B π S P)
include hφ

omit ha in
theorem typeCorr_isAdmissibleType_iff {X Y : Set W} (hc : h.TypeCorr φ a X Y) :
    IsAdmissibleType S X ↔ IsAdmissibleType S Y := by
  obtain ⟨hX, hY, he⟩ := hc
  rw [← h.isAdmissibleParabolic_conjugate_iff hX 1, conjugateSubgroup_one, ← hφ, he,
    h.isAdmissibleParabolic_conjugate_iff hY]

/-- `φ` maps the type of each component onto the type of a component. -/
theorem exists_typeCorr_componentSet (c : Component S) :
    ∃ d : Component S, h.TypeCorr φ a (componentSet c) (componentSet d) := by
  obtain ⟨Y, hc⟩ := h.exists_typeCorr_left ha (componentSet_subset c)
  have hY : Y ⊆ S := hc.2.1
  obtain ⟨d, hdY⟩ := exists_componentSet_subset_of_not_isAdmissibleType hY
    (fun hYa => not_isAdmissibleType_componentSet c ((h.typeCorr_isAdmissibleType_iff hφ hc).mpr hYa))
  obtain ⟨Z, hZ⟩ := h.exists_typeCorr_right ha (componentSet_subset d)
  have hZc : Z ⊆ componentSet c := (h.typeCorr_subset_iff hZ hc).mpr hdY
  obtain ⟨e, heZ⟩ := exists_componentSet_subset_of_not_isAdmissibleType
    (hZc.trans (componentSet_subset c))
    (fun hZa => not_isAdmissibleType_componentSet d ((h.typeCorr_isAdmissibleType_iff hφ hZ).mp hZa))
  obtain ⟨x, hx⟩ := componentSet_nonempty e
  have hec : e = c := eq_of_mem_componentSet hx (hZc (heZ hx))
  subst hec
  have hZeq : Z = componentSet e := subset_antisymm hZc heZ
  subst hZeq
  exact ⟨d, hZ⟩

omit hφ in
/-- `φ` maps the type `S \ {s}` of a vertex of the component `c` onto the type
`S \ {t}` with `t` in the corresponding component. -/
theorem exists_typeCorr_sdiff_singleton {c d : Component S}
    (hcd : h.TypeCorr φ a (componentSet c) (componentSet d)) {s : W}
    (hs : s ∈ componentSet c) :
    ∃ t ∈ componentSet d, h.TypeCorr φ a (S \ {s}) (S \ {t}) := by
  have hsS := componentSet_subset c hs
  obtain ⟨Y, hY⟩ := h.exists_typeCorr_left ha (Set.sdiff_subset : S \ {s} ⊆ S)
  have hYS : Y ≠ S := by
    rintro rfl
    have := (h.typeCorr_subset_iff h.typeCorr_self hY).mpr subset_rfl
    exact (this hsS).2 rfl
  obtain ⟨t, htS, htY⟩ : ∃ t ∈ S, t ∉ Y := by
    by_contra hall
    exact hYS (subset_antisymm hY.2.1 fun t ht => by_contra fun htY => hall ⟨t, ht, htY⟩)
  obtain ⟨Z, hZ⟩ := h.exists_typeCorr_right ha (Set.sdiff_subset : S \ {t} ⊆ S)
  have hYt : Y ⊆ S \ {t} := fun x hx => ⟨hY.2.1 hx, fun hxt => htY ((Set.mem_singleton_iff.mp hxt) ▸ hx)⟩
  have hsZ : S \ {s} ⊆ Z := (h.typeCorr_subset_iff hY hZ).mpr hYt
  have hsnZ : s ∉ Z := by
    intro hsZ'
    have hSZ : S ⊆ Z := fun x hx => by
      by_cases hxs : x = s
      · exact hxs ▸ hsZ'
      · exact hsZ ⟨hx, hxs⟩
    have := (h.typeCorr_subset_iff h.typeCorr_self hZ).mp hSZ
    exact (this htS).2 rfl
  have hZeq : Z = S \ {s} := subset_antisymm
    (fun x hx => ⟨hZ.1 hx, fun hxs => hsnZ ((Set.mem_singleton_iff.mp hxs) ▸ hx)⟩) hsZ
  have hYeq : Y = S \ {t} := h.typeCorr_right_unique hY (hZeq ▸ hZ)
  subst hYeq
  refine ⟨t, ?_, hY⟩
  have hnot : ¬ componentSet c ⊆ S \ {s} := fun hsub => (hsub hs).2 rfl
  rw [h.typeCorr_subset_iff hcd hY] at hnot
  obtain ⟨x, hxd, hxt⟩ := Set.not_subset.mp hnot
  have hxt' : x = t := by
    by_contra hne
    exact hxt ⟨componentSet_subset d hxd, hne⟩
  exact hxt' ▸ hxd

end TypeCorr

/-! ### Automorphisms preserving admissible parabolic subgroups -/

section Automorphism

variable {φ : G ≃* G} (hφ : ∀ P : Subgroup G,
  IsAdmissibleParabolic B π S (P.map φ.toMonoidHom) ↔ IsAdmissibleParabolic B π S P)
include hφ

/-- An automorphism preserving admissible parabolic subgroups maps `B` to a
conjugate of `B`. -/
theorem exists_map_borel_eq : ∃ a : G, B.map φ.toMonoidHom = conjugateSubgroup a B := by
  obtain ⟨g, X, hX, hgX⟩ :=
    h.exists_eq_conjugate_of_isAdmissibleParabolic ((hφ B).mpr h.isAdmissibleParabolic_borel)
  have hle : conjugateSubgroup g B ≤ B.map φ.toMonoidHom := by
    rw [hgX]
    exact conjugateSubgroup_mono g (h.le_of_coe_eq rfl)
  have hQ : IsAdmissibleParabolic B π S ((conjugateSubgroup g B).map φ.symm.toMonoidHom) := by
    rw [← hφ, map_map_symm]
    exact h.isAdmissibleParabolic_conjugate_borel g
  have hQB : (conjugateSubgroup g B).map φ.symm.toMonoidHom ≤ B := by
    have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hle
    rwa [map_symm_map] at this
  have hQeq : (conjugateSubgroup g B).map φ.symm.toMonoidHom = B := by
    simpa using h.eq_conjugate_borel_of_isAdmissible_of_le hQ 1 (by simpa using hQB)
  refine ⟨g, ?_⟩
  have := congrArg (Subgroup.map φ.toMonoidHom) hQeq
  rw [map_map_symm] at this
  exact this.symm

omit h in
/-- The inverse automorphism also preserves admissible parabolic subgroups. -/
theorem symm_isAdmissibleParabolic_iff (P : Subgroup G) :
    IsAdmissibleParabolic B π S (P.map φ.symm.toMonoidHom) ↔ IsAdmissibleParabolic B π S P := by
  have := hφ (P.map φ.symm.toMonoidHom)
  rw [map_map_symm] at this
  exact this.symm

/-- `φ` maps the vertices of each component to the vertices of one component. -/
theorem exists_component_map : ∃ σ : Component S → Component S, ∀ c (Q : Subgroup G),
    h.IsComponentVertex c Q → h.IsComponentVertex (σ c) (Q.map φ.toMonoidHom) := by
  obtain ⟨a, ha⟩ := h.exists_map_borel_eq hφ
  choose σ hσ using h.exists_typeCorr_componentSet ha hφ
  refine ⟨σ, fun c Q hQ => ?_⟩
  obtain ⟨g, s, hs, rfl⟩ := hQ
  obtain ⟨t, ht, hX', hY', hst⟩ := h.exists_typeCorr_sdiff_singleton ha (hσ c) hs
  refine ⟨φ g * a, t, ht, ?_⟩
  rw [maximalParabolic, map_conjugateSubgroup, hst, ← conjugateSubgroup_mul]
  rfl

omit hφ in
/-- A component vertex belongs to exactly one component. -/
theorem eq_of_isComponentVertex {c d : Component S} {Q : Subgroup G}
    (hc : h.IsComponentVertex c Q) (hd : h.IsComponentVertex d Q) : c = d := by
  obtain ⟨g, s, hs, rfl⟩ := hc
  obtain ⟨k, t, ht, he⟩ := hd
  have hst := h.eq_of_conjugateSubgroup_eq Set.sdiff_subset Set.sdiff_subset g k he
  have hst' : s = t := by
    by_contra hne
    have hsS : s ∈ S \ {t} := ⟨componentSet_subset c hs, hne⟩
    rw [← hst] at hsS
    exact hsS.2 rfl
  subst hst'
  exact eq_of_mem_componentSet hs ht

/-- The permutation of the components induced by `φ`. -/
theorem exists_componentPerm : ∃ σ : Equiv.Perm (Component S), ∀ c (Q : Subgroup G),
    h.IsComponentVertex (σ c) (Q.map φ.toMonoidHom) ↔ h.IsComponentVertex c Q := by
  obtain ⟨σ₁, h₁⟩ := h.exists_component_map hφ
  obtain ⟨σ₂, h₂⟩ := h.exists_component_map (φ := φ.symm) (symm_isAdmissibleParabolic_iff hφ)
  have key : ∀ c, σ₂ (σ₁ c) = c := fun c => by
    obtain ⟨s, hs⟩ := componentSet_nonempty c
    have hQ : h.IsComponentVertex c (h.maximalParabolic 1 s) := ⟨1, s, hs, rfl⟩
    have := h₂ _ _ (h₁ c _ hQ)
    rw [map_symm_map] at this
    exact h.eq_of_isComponentVertex this hQ
  have key' : ∀ d, σ₁ (σ₂ d) = d := fun d => by
    obtain ⟨s, hs⟩ := componentSet_nonempty d
    have hQ : h.IsComponentVertex d (h.maximalParabolic 1 s) := ⟨1, s, hs, rfl⟩
    have := h₁ _ _ (h₂ d _ hQ)
    rw [map_map_symm] at this
    exact h.eq_of_isComponentVertex this hQ
  refine ⟨⟨σ₁, σ₂, key, key'⟩, fun c Q => ⟨fun hQ => ?_, h₁ c Q⟩⟩
  have := h₂ _ _ hQ
  rwa [map_symm_map, Equiv.coe_fn_mk, key] at this

end Automorphism

/-! ### The induced polysimplicial vertex map -/

section VertexMap

variable {φ : G ≃* G} {σ : Equiv.Perm (Component S)}
  (hσ : ∀ c (Q : Subgroup G),
    h.IsComponentVertex (σ c) (Q.map φ.toMonoidHom) ↔ h.IsComponentVertex c Q)

/-- `φ` as a bijection from the vertices of `c` to those of `σ c`. -/
def componentVertexMapEquiv (c : Component S) :
    h.ComponentVertex c ≃ h.ComponentVertex (σ c) where
  toFun Q := ⟨Q.1.map φ.toMonoidHom, (hσ c Q.1).mpr Q.2⟩
  invFun Q' := ⟨Q'.1.map φ.symm.toMonoidHom, (hσ c _).mp (by rw [map_map_symm]; exact Q'.2)⟩
  left_inv Q := Subtype.ext (map_symm_map φ Q.1)
  right_inv Q' := Subtype.ext (map_map_symm φ Q'.1)

@[simp] theorem coe_componentVertexMapEquiv (c : Component S) (Q : h.ComponentVertex c) :
    (h.componentVertexMapEquiv hσ c Q).1 = Q.1.map φ.toMonoidHom :=
  rfl

/-- The vertex permutation of the polysimplicial complex induced by `φ`: the
coordinate `σ c` of the image is the image of the coordinate `c`. -/
def autVertexEquiv : (∀ c, h.ComponentVertex c) ≃ (∀ c, h.ComponentVertex c) :=
  Equiv.piCongr σ (h.componentVertexMapEquiv hσ)

theorem autVertexEquiv_apply (x : ∀ c, h.ComponentVertex c) (c : Component S) :
    h.autVertexEquiv hσ x (σ c) = h.componentVertexMapEquiv hσ c (x c) :=
  Equiv.piCongr_apply_apply σ _ x c

/-- The coordinate `σ c` of the image depends only on the coordinate `c`. -/
theorem respectsCoordinateFibers_autVertexEquiv :
    Langlands.Geometry.Building.AbstractBuilding.RespectsCoordinateFibers σ
      (h.autVertexEquiv hσ) := by
  intro c x y hxy
  rw [h.autVertexEquiv_apply hσ x c, h.autVertexEquiv_apply hσ y c, hxy]

theorem autVertexEquiv_mem_restrictedBox_iff (P : Subgroup G) (x : ∀ c, h.ComponentVertex c) :
    h.autVertexEquiv hσ x ∈ h.restrictedBox (P.map φ.toMonoidHom) ↔ x ∈ h.restrictedBox P := by
  simp only [restrictedBox, Set.mem_univ_pi]
  constructor
  · intro hx c
    have := hx (σ c)
    rw [h.autVertexEquiv_apply hσ x c, mem_componentFace, coe_componentVertexMapEquiv,
      map_le_map_iff_equiv] at this
    exact this
  · intro hx d
    obtain ⟨c, rfl⟩ := σ.surjective d
    rw [h.autVertexEquiv_apply hσ x c, mem_componentFace, coe_componentVertexMapEquiv,
      map_le_map_iff_equiv]
    exact hx c

/-- `φ` maps the product of component simplices of `P` onto that of `φ(P)`. -/
theorem restrictedBox_map (P : Subgroup G) :
    h.restrictedBox (P.map φ.toMonoidHom) = h.autVertexEquiv hσ '' h.restrictedBox P := by
  ext y
  constructor
  · intro hy
    refine ⟨(h.autVertexEquiv hσ).symm y, ?_, Equiv.apply_symm_apply _ y⟩
    rw [← h.autVertexEquiv_mem_restrictedBox_iff hσ, Equiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    exact (h.autVertexEquiv_mem_restrictedBox_iff hσ P x).mpr hx

end VertexMap

end IsTitsSystem

end Langlands.Group
