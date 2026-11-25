/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.AdicTowerStructure
public import WeilConjectures.Algebra.Module.AdicTowerLattice
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The `ℓ`-adic image tower of an Artin-Rees tower

Let `(Hₙ)` be a tower in an abelian category and `ℓ c : ℕ`. The **`ℓ`-adic image tower**
`G'ₘ = ℓᶜ · im(H_{m+2c} ⟶ H_{m+c}) ⊆ H_{m+c}` (`CategoryTheory.Functor.adicImageTower`) is the
image of `ψₘ = ℓᶜ ∘ (H_{m+2c} ⟶ H_{m+c})`, with the inclusion
`G'ₘ ⟶ H_{m+c}` (`CategoryTheory.Functor.adicImageTowerι`).

Think of `Hₙ = Rʲf_* Gₙ` for an `ℓ`-adic tower `(Gₙ)` along a smooth proper morphism: at every
geometric point the tower of stalks is Artin-Rees isomorphic to `(L / ℓⁿ)ₙ` with `L` finitely
generated, with constants independent of the point, and `ℓᶜ` kills the torsion of `L`. Then the
stalks of `G'ₘ` are `ℓᶜL / ℓᵐ⁺ᶜL ≅ (Λ / ℓᵐ)ʳ`, `r` the rank of the free module `ℓᶜ L`.

The results of this file are, for a functor `Φ` to modules preserving monomorphisms and
epimorphisms (a stalk functor), the elementwise statements at `Φ` needed to show that `G'` is an
exact `ℓ`-adic tower: if the tower `(Φ Hₙ)ₙ` is Artin-Rees with constant `c` and
`ℓ`-adically separated, the transition maps of `(Φ G'ₙ)` are surjective with kernel `ℓⁿ`
(`CategoryTheory.Functor.exists_pow_smul_eq_of_map_adicImageTower_map_eq_zero`,
`CategoryTheory.Functor.surjective_map_adicImageTower_map`), and if moreover `ℓᶜ` kills the
torsion of `lim Φ Hₙ` the tower is flat
(`CategoryTheory.Functor.exists_pow_smul_eq_of_pow_smul_eq_zero_adicImageTower`), with
`Φ G'ₘ ≅ (Λ / ℓᵐ)ʳ` over a discrete valuation ring
(`CategoryTheory.Functor.exists_linearEquiv_map_adicImageTower`). On the other hand, the
cokernel of `G'ₘ ⟶ H_{m+c}` is killed by `ℓ²ᶜ` as soon as `ℓᶜ : H_{m+c} ⟶ H_{m+c}` factors
through the transition map `H_{m+2c} ⟶ H_{m+c}`
(`CategoryTheory.Functor.pow_smul_cokernel_π_adicImageTowerι_eq_zero`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor

variable {C : Type*} [Category C] [Abelian C] (H : ℕᵒᵖ ⥤ C) (ℓ c : ℕ)

/-- The map `ψₘ = ℓᶜ ∘ (H_{m+2c} ⟶ H_{m+c})` whose image is the `m`-th term of the `ℓ`-adic image
tower. -/
abbrev adicImageTowerMap (m : ℕ) : H.obj (op (m + c + c)) ⟶ H.obj (op (m + c)) :=
  H.map (homOfLE (Nat.le_add_right (m + c) c)).op ≫ (ℓ ^ c • 𝟙 _)

/-- The maps `ψₘ` commute with the transition maps of `H`. -/
lemma adicImageTowerMap_comm {m k : ℕ} (h : m ≤ k) :
    H.map (homOfLE (by omega : m + c + c ≤ k + c + c)).op ≫ H.adicImageTowerMap ℓ c m =
      H.adicImageTowerMap ℓ c k ≫ H.map (homOfLE (by omega : m + c ≤ k + c)).op := by
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
    ← H.map_comp]
  rfl

/-- The tower of arrows `ψₘ = ℓᶜ ∘ (H_{m+2c} ⟶ H_{m+c})`. -/
noncomputable def adicImageTowerArrow : ℕᵒᵖ ⥤ Arrow C where
  obj m := Arrow.mk (H.adicImageTowerMap ℓ c m.unop)
  map {m k} h := Arrow.homMk (H.map (homOfLE (by have := leOfHom h.unop; omega)).op)
    (H.map (homOfLE (by have := leOfHom h.unop; omega)).op)
    (H.adicImageTowerMap_comm ℓ c (leOfHom h.unop))
  map_id m := by
    ext
    · exact H.map_id _
    · exact H.map_id _
  map_comp f g := by
    ext
    · exact H.map_comp _ _
    · exact H.map_comp _ _

/-- The **`ℓ`-adic image tower** `G'ₘ = im(ℓᶜ ∘ (H_{m+2c} ⟶ H_{m+c})) = ℓᶜ · im(H_{m+2c} ⟶ H_{m+c})`
of a tower `H`. -/
noncomputable def adicImageTower : ℕᵒᵖ ⥤ C :=
  H.adicImageTowerArrow ℓ c ⋙ im

/-- The `m`-th term of the `ℓ`-adic image tower is the image of `ψₘ`. -/
lemma adicImageTower_obj (m : ℕ) :
    (H.adicImageTower ℓ c).obj (op m) = image (H.adicImageTowerMap ℓ c m) :=
  rfl

/-- The epimorphism `H_{m+2c} ⟶ G'ₘ` onto the `m`-th term of the `ℓ`-adic image tower. -/
noncomputable def adicImageTowerπ (m : ℕ) :
    H.obj (op (m + c + c)) ⟶ (H.adicImageTower ℓ c).obj (op m) :=
  factorThruImage (H.adicImageTowerMap ℓ c m)

/-- The inclusion `G'ₘ ⟶ H_{m+c}` of the `m`-th term of the `ℓ`-adic image tower. -/
noncomputable def adicImageTowerι (m : ℕ) :
    (H.adicImageTower ℓ c).obj (op m) ⟶ H.obj (op (m + c)) :=
  image.ι (H.adicImageTowerMap ℓ c m)

/-- `H_{m+2c} ⟶ G'ₘ` is an epimorphism. -/
instance (m : ℕ) : Epi (H.adicImageTowerπ ℓ c m) := by
  dsimp [adicImageTowerπ]
  infer_instance

/-- `G'ₘ ⟶ H_{m+c}` is a monomorphism. -/
instance (m : ℕ) : Mono (H.adicImageTowerι ℓ c m) := by
  dsimp [adicImageTowerι]
  infer_instance

/-- `ψₘ` factors as `H_{m+2c} ⟶ G'ₘ ⟶ H_{m+c}`. -/
@[reassoc (attr := simp)]
lemma adicImageTowerπ_ι (m : ℕ) :
    H.adicImageTowerπ ℓ c m ≫ H.adicImageTowerι ℓ c m = H.adicImageTowerMap ℓ c m :=
  image.fac _

/-- The transition maps of the `ℓ`-adic image tower are restrictions of those of `H`. -/
@[reassoc]
lemma adicImageTower_map_comp_ι {m k : ℕ} (h : m ≤ k) :
    (H.adicImageTower ℓ c).map (homOfLE h).op ≫ H.adicImageTowerι ℓ c m =
      H.adicImageTowerι ℓ c k ≫ H.map (homOfLE (Nat.add_le_add_right h c)).op :=
  image.map_ι _

/-- The shift `(H_{n+c})ₙ` of a tower `H`. -/
abbrev towerShift (H : ℕᵒᵖ ⥤ C) (c : ℕ) : ℕᵒᵖ ⥤ C :=
  (Monotone.functor (f := fun n : ℕ ↦ n + c) fun _ _ h ↦ Nat.add_le_add_right h c).op ⋙ H

/-- The inclusion `G' ⟶ (H_{m+c})ₘ` of the `ℓ`-adic image tower, as a morphism of towers. -/
noncomputable def adicImageTowerHom : H.adicImageTower ℓ c ⟶ H.towerShift c where
  app m := H.adicImageTowerι ℓ c m.unop
  naturality _ _ h := H.adicImageTower_map_comp_ι ℓ c (leOfHom h.unop)

/-- The components of `G' ⟶ (H_{m+c})ₘ` are the inclusions `G'ₘ ⟶ H_{m+c}`. -/
@[simp]
lemma adicImageTowerHom_app (m : ℕ) :
    (H.adicImageTowerHom ℓ c).app (op m) = H.adicImageTowerι ℓ c m :=
  rfl

/-- `ℓᵐ` kills the `m`-th term of the `ℓ`-adic image tower when `ℓⁿ` kills `Hₙ` for all `n`. -/
lemma adicImageTower_pow_smul_id_eq_zero (hzero : ∀ n : ℕ, ℓ ^ n • 𝟙 (H.obj (op n)) = 0)
    (m : ℕ) : ℓ ^ m • 𝟙 ((H.adicImageTower ℓ c).obj (op m)) = 0 := by
  rw [← cancel_mono (H.adicImageTowerι ℓ c m), ← cancel_epi (H.adicImageTowerπ ℓ c m),
    Limits.zero_comp, Limits.comp_zero, Preadditive.nsmul_comp, Category.id_comp,
    Preadditive.comp_nsmul, adicImageTowerπ_ι, adicImageTowerMap, Preadditive.comp_nsmul,
    smul_smul, ← pow_add, ← Preadditive.comp_nsmul, hzero, Limits.comp_zero]

/-- **The cokernel of `G'ₘ ⟶ H_{m+c}` is killed by `ℓ²ᶜ`** as soon as `ℓᶜ : Hₙ ⟶ Hₙ` factors
through the transition map `H_{n+c} ⟶ Hₙ`, by `ι : Hₙ ⟶ H_{n+c}`: then
`ℓ²ᶜ = ψₘ ∘ ι` on `H_{m+c}`. -/
lemma pow_smul_cokernel_π_adicImageTowerι_eq_zero
    (ι : ∀ n : ℕ, H.obj (op n) ⟶ H.obj (op (n + c)))
    (hι : ∀ n : ℕ, ι n ≫ H.map (homOfLE (Nat.le_add_right n c)).op = ℓ ^ c • 𝟙 _) (m : ℕ) :
    ℓ ^ (c + c) • cokernel.π (H.adicImageTowerι ℓ c m) = 0 := by
  have h : ℓ ^ (c + c) • 𝟙 (H.obj (op (m + c))) =
      ι (m + c) ≫ H.adicImageTowerπ ℓ c m ≫ H.adicImageTowerι ℓ c m := by
    rw [adicImageTowerπ_ι, reassoc_of% (hι (m + c)), Preadditive.nsmul_comp,
      Category.id_comp, pow_add, mul_smul]
  rw [← Category.id_comp (cokernel.π _), ← Preadditive.nsmul_comp, h, Category.assoc,
    Category.assoc, cokernel.condition, Limits.comp_zero, Limits.comp_zero]

section AdicTowerStructure

variable {D : Type*} [Category D] [Abelian D] {G : ℕᵒᵖ ⥤ D} (A : AdicTowerStructure G ℓ)
  (T : D ⥤ C) [T.Additive]

include A in
/-- `ℓⁿ` kills `T Gₙ` for an `ℓ`-adic tower `G` and an additive functor `T`. -/
lemma pow_smul_id_eq_zero_of_adicTowerStructure (n : ℕ) :
    ℓ ^ n • 𝟙 ((G ⋙ T).obj (op n)) = 0 := by
  rw [Functor.comp_obj, ← T.map_id, ← T.map_nsmul, A.pow_smul_id_eq_zero, T.map_zero]

include A in
/-- **The cokernel of `G'ₘ ⟶ T G_{m+c}` is killed by `ℓ²ᶜ`** for the `ℓ`-adic image tower of
`T G`, `G` an `ℓ`-adic tower and `T` an additive functor: `ℓᶜ : T Gₙ ⟶ T Gₙ` factors through
the transition map `T G_{n+c} ⟶ T Gₙ` by `T ιₙ꜀`. -/
lemma pow_smul_cokernel_π_adicImageTowerι_eq_zero_of_adicTowerStructure (m : ℕ) :
    ℓ ^ (c + c) • cokernel.π ((G ⋙ T).adicImageTowerι ℓ c m) = 0 :=
  (G ⋙ T).pow_smul_cokernel_π_adicImageTowerι_eq_zero ℓ c (fun n ↦ T.map (A.ι n c))
    (fun n ↦ by
      rw [Functor.comp_map, ← T.map_comp, A.ι_comp_map, T.map_nsmul, T.map_id]
      rfl) m

end AdicTowerStructure

section Stalk

variable {R : Type u} [CommRing R] (Φ : C ⥤ ModuleCat.{v} R)

/-- The inclusion `Φ G'ₘ ⟶ Φ H_{m+c}` is injective. -/
lemma injective_map_adicImageTowerι [Φ.PreservesMonomorphisms] (m : ℕ) :
    Function.Injective (Φ.map (H.adicImageTowerι ℓ c m)) :=
  (ModuleCat.mono_iff_injective _).1 (Φ.map_mono _)

/-- The transition maps of `Φ G'` are restrictions of those of `Φ H`. -/
lemma map_adicImageTowerι_map {m k : ℕ} (h : m ≤ k)
    (w : Φ.obj ((H.adicImageTower ℓ c).obj (op k))) :
    Φ.map (H.adicImageTowerι ℓ c m) (Φ.map ((H.adicImageTower ℓ c).map (homOfLE h).op) w) =
      ModuleCat.towerMap (H ⋙ Φ) (Nat.add_le_add_right h c) (Φ.map (H.adicImageTowerι ℓ c k) w) :=
  by
  rw [← ConcreteCategory.comp_apply, ← Φ.map_comp, adicImageTower_map_comp_ι, Φ.map_comp,
    ConcreteCategory.comp_apply]
  rfl

variable [Φ.Additive]

/-- **The image of `Φ G'ₘ ⟶ Φ H_{m+c}`** is `ℓᶜ` times the image of `lim Φ Hₙ`, when the tower
`(Φ Hₙ)` is Artin-Rees with constant `c`: the image of `Φ H_{m+c+c} ⟶ Φ H_{m+c}` is the image
of `lim Φ Hₙ`. -/
lemma mem_range_map_adicImageTowerι_iff [Φ.PreservesEpimorphisms]
    (hAR : ∀ (m : ℕ) (z : (H ⋙ Φ).obj (op (m + c))), ∃ x : ModuleCat.sectionsSubmodule (H ⋙ Φ),
      x.1 (op m) = ModuleCat.towerMap (H ⋙ Φ) (Nat.le_add_right m c) z)
    (m : ℕ) (w : Φ.obj (H.obj (op (m + c)))) :
    w ∈ Set.range (Φ.map (H.adicImageTowerι ℓ c m)) ↔
      ∃ x : ModuleCat.sectionsSubmodule (H ⋙ Φ), ℓ ^ c • x.1 (op (m + c)) = w := by
  have hsurj : Function.Surjective (Φ.map (H.adicImageTowerπ ℓ c m)) :=
    (ModuleCat.epi_iff_surjective _).1 (Φ.map_epi _)
  have hψ (z : Φ.obj (H.obj (op (m + c + c)))) :
      Φ.map (H.adicImageTowerι ℓ c m) (Φ.map (H.adicImageTowerπ ℓ c m) z) =
        ℓ ^ c • ModuleCat.towerMap (H ⋙ Φ) (Nat.le_add_right (m + c) c) z := by
    rw [← ConcreteCategory.comp_apply, ← Φ.map_comp, adicImageTowerπ_ι, Φ.map_comp,
      Φ.map_nsmul, CategoryTheory.Functor.map_id, ConcreteCategory.comp_apply]
    rfl
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj w
    obtain ⟨x, hx⟩ := hAR (m + c) z
    exact ⟨x, by rw [hψ, ← hx]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨Φ.map (H.adicImageTowerπ ℓ c m) (x.1 (op (m + c + c))), ?_⟩
    rw [hψ]
    exact congrArg _ ((ModuleCat.mem_sectionsSubmodule_iff _ _).1 x.2 _)

variable [Φ.PreservesMonomorphisms] [Φ.PreservesEpimorphisms]
  (hAR : ∀ (m : ℕ) (z : (H ⋙ Φ).obj (op (m + c))), ∃ x : ModuleCat.sectionsSubmodule (H ⋙ Φ),
    x.1 (op m) = ModuleCat.towerMap (H ⋙ Φ) (Nat.le_add_right m c) z)
  (hker : ∀ (m : ℕ) (x : ModuleCat.sectionsSubmodule (H ⋙ Φ)),
    x.1 (op m) = 0 ↔ ∃ y : ModuleCat.sectionsSubmodule (H ⋙ Φ), ℓ ^ m • y = x)

omit [Φ.PreservesMonomorphisms] in
include hAR in
/-- Every element of `Φ G'ₘ` is `ℓᶜ x_{m+c}` for an element `x` of `lim Φ Hₙ`. -/
lemma exists_map_adicImageTowerι_eq (m : ℕ) (w : Φ.obj ((H.adicImageTower ℓ c).obj (op m))) :
    ∃ x : ModuleCat.sectionsSubmodule (H ⋙ Φ),
      ℓ ^ c • x.1 (op (m + c)) = Φ.map (H.adicImageTowerι ℓ c m) w :=
  (H.mem_range_map_adicImageTowerι_iff ℓ c Φ hAR m _).1 ⟨w, rfl⟩

include hAR in
/-- **The transition maps of `Φ G'` are surjective.** -/
lemma surjective_map_adicImageTower_map {n k : ℕ} (h : n ≤ k) :
    Function.Surjective (Φ.map ((H.adicImageTower ℓ c).map (homOfLE h).op)) := fun w ↦ by
  obtain ⟨x, hx⟩ := H.exists_map_adicImageTowerι_eq ℓ c Φ hAR n w
  obtain ⟨w', hw'⟩ := (H.mem_range_map_adicImageTowerι_iff ℓ c Φ hAR k
    (ℓ ^ c • x.1 (op (k + c)))).2 ⟨x, rfl⟩
  refine ⟨w', H.injective_map_adicImageTowerι ℓ c Φ n ?_⟩
  rw [map_adicImageTowerι_map, hw', _root_.map_nsmul, ← hx]
  exact congrArg _ ((ModuleCat.mem_sectionsSubmodule_iff _ _).1 x.2 _)

include hAR hker in
/-- **The kernel of the transition map `Φ G'ₖ ⟶ Φ G'ₙ` is `ℓⁿ Φ G'ₖ`.** -/
lemma exists_pow_smul_eq_of_map_adicImageTower_map_eq_zero {n k : ℕ} (h : n ≤ k)
    (w : Φ.obj ((H.adicImageTower ℓ c).obj (op k)))
    (hw : Φ.map ((H.adicImageTower ℓ c).map (homOfLE h).op) w = 0) :
    ∃ w', ℓ ^ n • w' = w := by
  obtain ⟨x, hx⟩ := H.exists_map_adicImageTowerι_eq ℓ c Φ hAR k w
  have h₀ : (ℓ ^ c • x).1 (op (n + c)) = 0 := by
    have := congrArg (Φ.map (H.adicImageTowerι ℓ c n)) hw
    rw [map_adicImageTowerι_map, ← hx, _root_.map_zero, _root_.map_nsmul,
      (ModuleCat.mem_sectionsSubmodule_iff _ _).1 x.2] at this
    exact this
  obtain ⟨y, hy⟩ := (hker (n + c) _).1 h₀
  obtain ⟨w', hw'⟩ := (H.mem_range_map_adicImageTowerι_iff ℓ c Φ hAR k
    (ℓ ^ c • y.1 (op (k + c)))).2 ⟨y, rfl⟩
  refine ⟨w', H.injective_map_adicImageTowerι ℓ c Φ k ?_⟩
  rw [_root_.map_nsmul, hw', ← hx, smul_smul, ← pow_add]
  exact congrArg (fun z : ModuleCat.sectionsSubmodule (H ⋙ Φ) ↦ z.1 (op (k + c))) hy

include hAR hker in
/-- **The tower `Φ G'` is flat**: the `ℓᵐ`-torsion of `Φ G'ₙ₊ₘ` is `ℓⁿ Φ G'ₙ₊ₘ`, when `ℓᶜ` kills
the `ℓ`-power torsion of `lim Φ Hₙ`. -/
lemma exists_pow_smul_eq_of_pow_smul_eq_zero_adicImageTower
    (htors : ∀ (y : ModuleCat.sectionsSubmodule (H ⋙ Φ)) (k : ℕ), ℓ ^ k • y = 0 → ℓ ^ c • y = 0)
    (n m : ℕ) (w : Φ.obj ((H.adicImageTower ℓ c).obj (op (n + m)))) (hw : ℓ ^ m • w = 0) :
    ∃ w', ℓ ^ n • w' = w := by
  obtain ⟨x, hx⟩ := H.exists_map_adicImageTowerι_eq ℓ c Φ hAR (n + m) w
  have h₀ : (ℓ ^ (m + c) • x).1 (op (n + m + c)) = 0 := by
    have := congrArg (Φ.map (H.adicImageTowerι ℓ c (n + m))) hw
    rw [_root_.map_nsmul, ← hx, _root_.map_zero, smul_smul, ← pow_add] at this
    exact this
  obtain ⟨y, hy⟩ := (hker (n + m + c) _).1 h₀
  have hv : ℓ ^ (m + c) • (x - ℓ ^ n • y) = 0 := by
    have e : m + c + n = n + m + c := by omega
    rw [smul_sub, smul_smul, ← pow_add, e, hy, sub_self]
  have hxy := htors _ _ hv
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hxy
  obtain ⟨w', hw'⟩ := (H.mem_range_map_adicImageTowerι_iff ℓ c Φ hAR (n + m)
    (ℓ ^ c • y.1 (op (n + m + c)))).2 ⟨y, rfl⟩
  refine ⟨w', H.injective_map_adicImageTowerι ℓ c Φ (n + m) ?_⟩
  rw [_root_.map_nsmul, hw', ← hx, smul_smul, ← pow_add, add_comm n c]
  exact (congrArg (fun z : ModuleCat.sectionsSubmodule (H ⋙ Φ) ↦ z.1 (op (n + m + c))) hxy).symm

include hAR hker in
/-- **`Φ G'ₘ ≅ (R / ℓᵐ)ʳ`.** Over a discrete valuation ring `R` in which `ℓ` is a nonzero nonunit,
if `lim Φ Hₙ` is finitely generated with `ℓ`-power torsion killed by `ℓᶜ`, then
`Φ G'ₘ ≅ ℓᶜL / ℓᵐ⁺ᶜL ≅ (R / ℓᵐ)ʳ` for all `m`, `r` being the rank of the free module `ℓᶜ L`. -/
theorem exists_linearEquiv_map_adicImageTower [IsDomain R] [IsDiscreteValuationRing R]
    (hℓ : (ℓ : R) ≠ 0) (hℓ' : ¬IsUnit (ℓ : R))
    [Module.Finite R (ModuleCat.sectionsSubmodule (H ⋙ Φ))]
    (htors : ∀ (y : ModuleCat.sectionsSubmodule (H ⋙ Φ)) (k : ℕ), ℓ ^ k • y = 0 → ℓ ^ c • y = 0) :
    ∃ r : ℕ, ∀ m : ℕ, Nonempty (Φ.obj ((H.adicImageTower ℓ c).obj (op m)) ≃ₗ[R]
      (Fin r → R ⧸ Ideal.span {(ℓ : R) ^ m})) := by
  obtain ⟨r, hr⟩ := Module.exists_linearEquiv_range_comp_nsmul.{_, _, v}
    (L := ModuleCat.sectionsSubmodule (H ⋙ Φ)) hℓ hℓ' htors
  refine ⟨r, fun m ↦ ?_⟩
  obtain ⟨e⟩ := hr m (ModuleCat.sectionsEval (H ⋙ Φ) (m + c)) fun x ↦ by
    rw [ModuleCat.sectionsEval_apply]
    exact hker (m + c) x
  have hrange : LinearMap.range (Φ.map (H.adicImageTowerι ℓ c m)).hom =
      LinearMap.range (ModuleCat.sectionsEval (H ⋙ Φ) (m + c) ∘ₗ (ℓ ^ c • LinearMap.id)) := by
    ext w
    have := H.mem_range_map_adicImageTowerι_iff ℓ c Φ hAR m w
    simp only [Set.mem_range] at this
    rw [LinearMap.mem_range]
    exact this
  exact ⟨LinearEquiv.ofInjective _ (H.injective_map_adicImageTowerι ℓ c Φ m) ≪≫ₗ
    LinearEquiv.ofEq _ _ hrange ≪≫ₗ e⟩

end Stalk

end CategoryTheory.Functor
