import Langlands.Sheaf.CompactSupport

/-! # Compact sections defined by actual neighborhood restrictions -/

noncomputable section

universe u r w

namespace Langlands.Sheaf.LocalSupport

open CategoryTheory TopologicalSpace Opposite

variable {R : Type r} [CommRing R] {X : Type u} [TopologicalSpace X]
  (F : (TopCat.of X).Presheaf (ModuleCat.{w} R))

/-- Restrict an actual global section to an actual open subset. -/
def restrict (U : Opens X) : F.obj (op ⊤) ⟶ F.obj (op U) :=
  F.map (homOfLE (show U ≤ ⊤ from le_top)).op

/-- A global section vanishes near a point if one open-neighborhood restriction is zero. -/
def VanishesNear (s : F.obj (op ⊤)) (x : X) : Prop :=
  ∃ U : Opens X, x ∈ U ∧ restrict F U s = 0

/-- Section support is the complement of its actual local vanishing locus. -/
def support (s : F.obj (op ⊤)) : Set X := {x | ¬ VanishesNear F s x}

/-- Iterated ordinary restriction equals direct restriction. -/
theorem restrict_of_le {U V : Opens X} (h : U ≤ V) (s : F.obj (op ⊤)) :
    F.map (homOfLE h).op (restrict F V s) = restrict F U s := by
  change (F.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫
    F.map (homOfLE h).op) s = _
  rw [← F.map_comp]
  rfl

/-- A vanishing restriction vanishes on every smaller open. -/
theorem restrict_zero_of_le {U V : Opens X} (h : U ≤ V) {s : F.obj (op ⊤)}
    (hs : restrict F V s = 0) : restrict F U s = 0 := by
  rw [← restrict_of_le F h s, hs, map_zero]

/-- Local vanishing is an open condition even before imposing the sheaf condition. -/
theorem isClosed_support (s : F.obj (op ⊤)) : IsClosed (support F s) := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hv : VanishesNear F s x := by simpa [support] using hx
  obtain ⟨U, hxU, hU⟩ := hv
  apply Filter.mem_of_superset (U.isOpen.mem_nhds hxU)
  intro y hy
  change ¬ ¬ VanishesNear F s y
  exact not_not.mpr ⟨U, hy, hU⟩

@[simp]
theorem vanishesNear_zero (x : X) : VanishesNear F 0 x :=
  ⟨⊤, trivial, map_zero _⟩

@[simp]
theorem support_zero : support F 0 = ∅ := by
  ext x
  simp [support]

/-- The intersection of two vanishing neighborhoods works for the sum. -/
theorem vanishesNear_add {s t : F.obj (op ⊤)} {x : X}
    (hs : VanishesNear F s x) (ht : VanishesNear F t x) :
    VanishesNear F (s + t) x := by
  obtain ⟨U, hxU, hU⟩ := hs
  obtain ⟨V, hxV, hV⟩ := ht
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ?_⟩
  have hs' := restrict_zero_of_le F (show U ⊓ V ≤ U from inf_le_left) hU
  have ht' := restrict_zero_of_le F (show U ⊓ V ≤ V from inf_le_right) hV
  rw [map_add, hs', ht', add_zero]

/-- Scalar multiplication preserves every vanishing neighborhood. -/
theorem vanishesNear_smul (a : R) {s : F.obj (op ⊤)} {x : X}
    (hs : VanishesNear F s x) : VanishesNear F (a • s) x := by
  obtain ⟨U, hxU, hU⟩ := hs
  exact ⟨U, hxU, by rw [map_smul, hU, smul_zero]⟩

theorem support_add_subset (s t : F.obj (op ⊤)) :
    support F (s + t) ⊆ support F s ∪ support F t := by
  classical
  intro x hx
  by_contra h
  exact hx (vanishesNear_add F (by simpa [support] using (not_or.mp h).1)
    (by simpa [support] using (not_or.mp h).2))

theorem support_smul_subset (a : R) (s : F.obj (op ⊤)) :
    support F (a • s) ⊆ support F s := by
  intro x hx hs
  exact hx (vanishesNear_smul F a hs)

variable {F}

/-- Naturality sends a zero neighborhood restriction to a zero restriction. -/
theorem vanishesNear_map {F' : (TopCat.of X).Presheaf (ModuleCat.{w} R)}
    (f : F ⟶ F') {s : F.obj (op ⊤)} {x : X} (hs : VanishesNear F s x) :
    VanishesNear F' (f.app (op ⊤) s) x := by
  obtain ⟨U, hxU, hU⟩ := hs
  refine ⟨U, hxU, ?_⟩
  have h := congrArg (fun k : F.obj (op ⊤) ⟶ F'.obj (op U) => k s)
    (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change f.app (op U) (restrict F U s) = restrict F' U (f.app (op ⊤) s) at h
  rw [hU, map_zero] at h
  exact h.symm

/-- A genuine presheaf morphism cannot enlarge local support. -/
theorem support_map_subset {F' : (TopCat.of X).Presheaf (ModuleCat.{w} R)}
    (f : F ⟶ F') (s : F.obj (op ⊤)) :
    support F' (f.app (op ⊤) s) ⊆ support F s := by
  intro x hx hs
  exact hx (vanishesNear_map f hs)

variable (F)

/-- All global sections with compact local support, with no universe identification. -/
def submodule : Submodule R (F.obj (op ⊤)) where
  carrier := {s | IsCompact (support F s)}
  zero_mem' := by simp
  add_mem' hs ht :=
    (hs.union ht).of_isClosed_subset (isClosed_support F _) (support_add_subset F _ _)
  smul_mem' a s hs :=
    hs.of_isClosed_subset (isClosed_support F _) (support_smul_subset F a s)

variable {F}

/-- Restriction of the actual global component of a presheaf morphism. -/
def map {F' : (TopCat.of X).Presheaf (ModuleCat.{w} R)} (f : F ⟶ F') :
    submodule F →ₗ[R] submodule F' :=
  (f.app (op ⊤)).hom.restrict (fun s hs =>
    hs.of_isClosed_subset (isClosed_support F' _) (support_map_subset f s))

/-- The compact-local-support section functor on full module presheaves. -/
def presheafFunctor :
    (TopCat.of X).Presheaf (ModuleCat.{w} R) ⥤ ModuleCat.{w} R where
  obj F := ModuleCat.of R (submodule F)
  map f := ModuleCat.ofHom (map f)
  map_id _ := by ext s; rfl
  map_comp _ _ := by ext s; rfl

/-- Forgetting the support condition is the actual natural section inclusion. -/
def inclusion : presheafFunctor (X := X) (R := R) ⟶
    (evaluation (Opens X)ᵒᵖ (ModuleCat.{w} R)).obj (op ⊤) where
  app F := ModuleCat.ofHom (submodule F).subtype
  naturality _ _ _ := by ext s; rfl

section StalkComparison

variable {S : Type u} [CommRing S]
  (P : (TopCat.of X).Presheaf (ModuleCat.{u} S))

/-- In the universes supported by Mathlib stalks, this is exactly germ vanishing. -/
theorem vanishesNear_iff_germ_zero (s : P.obj (op ⊤)) (x : X) :
    VanishesNear P s x ↔ P.Γgerm x s = 0 := by
  constructor
  · rintro ⟨U, hxU, hU⟩
    rw [← P.Γgerm_res_apply x hxU s (i := homOfLE (show U ≤ ⊤ from le_top))]
    change P.germ U x hxU (restrict P U s) = 0
    rw [hU]
    exact map_zero _
  · intro hx
    obtain ⟨W, hxW, i, j, hW⟩ :=
      P.germ_eq x (U := ⊤) (V := ⊤) trivial trivial s 0
        (by simpa [TopCat.Presheaf.Γgerm] using hx)
    refine ⟨W, hxW, ?_⟩
    have hz : P.map i.op s = 0 := by simpa using hW
    exact hz

/-- The new restriction-defined support agrees with the existing actual stalk support. -/
theorem support_eq_stalkSupport (s : P.obj (op ⊤)) :
    support P s = Langlands.Sheaf.CompactSupport.support P s := by
  ext x
  exact not_congr (vanishesNear_iff_germ_zero P s x)

/-- No compact section is gained or lost by the local-vanishing formulation. -/
theorem submodule_eq_stalkSubmodule :
    submodule P = Langlands.Sheaf.CompactSupport.submodule P := by
  ext s
  change IsCompact (support P s) ↔
    IsCompact (Langlands.Sheaf.CompactSupport.support P s)
  rw [support_eq_stalkSupport]

end StalkComparison

end Langlands.Sheaf.LocalSupport
