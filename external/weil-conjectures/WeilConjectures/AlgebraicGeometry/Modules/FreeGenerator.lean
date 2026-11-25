/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Free generators of a module on a scheme

A section `e` of an `𝒪_X`-module `M` over an open `U` is a *free generator* if every section of
`M` over an open `V ⊆ U` is uniquely of the form `r • e|_V`; equivalently, `r ↦ r • e`
trivializes `M|_U ≅ 𝒪_U`. Invertible modules have free generators locally.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator`: a section trivializing a module.
- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.coeff`: the coefficient of a section with
  respect to a free generator.
- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.overIso`: the trivialization
  `M|_U ≅ 𝒪_U` given by a free generator.
- `AlgebraicGeometry.Scheme.Modules.glueHom`: the morphism `M ⟶ N` sending free generators of
  `M` on an open cover to compatible sections of `N`.
- `AlgebraicGeometry.Scheme.Modules.pullbackSection`: the pullback `g^* m` of a section `m`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator`: invertible modules are locally
  trivial.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_of_mem`: being a free generator is local.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_of_locally`: a section which is locally a
  generator, and by which multiplication is injective, is a free generator.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_isFreeGenerator`: two modules with free
  generators on a common open cover with the same transition functions are isomorphic.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_of_isIso_restrict`: a morphism `𝒪_X ⟶ M`
  which is an isomorphism over `U` gives a free generator of `M` on `U`.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_pullbackSection`: the pullback `g^* e` of
  such a free generator is a free generator of `g^* M` on `g⁻¹ U`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- Restricting a function twice is restricting it along the composite. -/
lemma presheaf_map_map_apply {U V W : X.Opens} (f : V ⟶ U) (g : W ⟶ V) (a : Γ(X, U)) :
    X.presheaf.map g.op (X.presheaf.map f.op a) = X.presheaf.map (g ≫ f).op a := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- Restricting a function along an endomorphism of an open does nothing. -/
lemma presheaf_map_id_apply {U : X.Opens} (f : U ⟶ U) (a : Γ(X, U)) :
    X.presheaf.map f.op a = a := by
  rw [Subsingleton.elim f (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl

variable (X) in
/-- The structure sheaf of `X` is a sheaf of types. -/
lemma isSheaf_presheaf_comp_forget :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (X.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose _ (CategoryTheory.forget CommRingCat)).obj X.sheaf).property

/-- Two sections of the structure sheaf over `W` agree if they agree on a covering sieve. -/
lemma ext_of_mem {W : X.Opens} {S : Sieve W} (hS : S ∈ Opens.grothendieckTopology X W)
    {a b : Γ(X, W)}
    (h : ∀ ⦃Z : X.Opens⦄ (l : Z ⟶ W), S l → X.presheaf.map l.op a = X.presheaf.map l.op b) :
    a = b :=
  (X.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext h

namespace Modules

variable {M N : X.Modules}

variable (M) in
/-- The underlying presheaf of types of a sheaf of modules is a sheaf. -/
lemma isSheaf_presheaf_comp_forget :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose (Opens.grothendieckTopology X) (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ⟨M.presheaf, M.isSheaf⟩).property

/-- A section `e` of `M` over `U` is a *free generator* of `M` on `U` if every section of `M`
over an open `V ⊆ U` is uniquely of the form `r • e|_V` with `r ∈ Γ(X, V)`; i.e. `e`
trivializes `M|_U ≅ 𝒪_U`. -/
def IsFreeGenerator {U : X.Opens} (e : Γ(M, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective fun r : Γ(X, V) ↦ r • M.presheaf.map (homOfLE h).op e

/-- Restricting a section of `M` twice is restricting it along the composite. -/
lemma presheaf_map_map_apply {U V W : X.Opens} (f : V ⟶ U) (g : W ⟶ V) (e : Γ(M, U)) :
    M.presheaf.map g.op (M.presheaf.map f.op e) = M.presheaf.map (g ≫ f).op e := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- Restricting a section of `M` along an endomorphism of an open does nothing. -/
lemma presheaf_map_id_apply {U : X.Opens} (f : U ⟶ U) (e : Γ(M, U)) :
    M.presheaf.map f.op e = e := by
  rw [Subsingleton.elim f (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Morphisms of modules commute with restriction of sections. -/
lemma Hom.app_presheaf_map (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) :=
  PresheafOfModules.naturality_apply φ.val i.op x

namespace IsFreeGenerator

variable {U : X.Opens} {e : Γ(M, U)}

/-- The restriction of a free generator to a smaller open is a free generator. -/
lemma map {V : X.Opens} (he : IsFreeGenerator e) (h : V ≤ U) :
    IsFreeGenerator (M.presheaf.map (homOfLE h).op e) := by
  intro W hW
  simp_rw [presheaf_map_map_apply]
  exact he W (hW.trans h)

/-- A free generator `e` on `U` gives a bijection `r ↦ r • e` from `Γ(X, U)` to `Γ(M, U)`. -/
lemma bijective (he : IsFreeGenerator e) : Function.Bijective fun r : Γ(X, U) ↦ r • e := by
  simpa only [presheaf_map_id_apply] using he U le_rfl

/-- A free generator `e` on `U` gives an injection `r ↦ r • e` of `Γ(X, U)` into `Γ(M, U)`. -/
lemma smul_left_injective (he : IsFreeGenerator e) :
    Function.Injective fun r : Γ(X, U) ↦ r • e :=
  he.bijective.1

/-- Every section over `U` is a multiple of a free generator on `U`. -/
lemma exists_smul_eq (he : IsFreeGenerator e) (m : Γ(M, U)) : ∃ r : Γ(X, U), r • e = m :=
  he.bijective.2 m

/-- Two free generators on the same open differ by a unit. -/
lemma exists_unit_smul_eq {e' : Γ(M, U)} (he : IsFreeGenerator e) (he' : IsFreeGenerator e') :
    ∃ u : Γ(X, U)ˣ, e' = u.1 • e := by
  obtain ⟨u, hu⟩ := he.exists_smul_eq e'
  obtain ⟨v, hv⟩ := he'.exists_smul_eq e
  have huv : v * u = 1 := he.smul_left_injective (by simp only [mul_smul, hu, hv, one_smul])
  exact ⟨⟨u, v, by rw [mul_comm, huv], huv⟩, hu.symm⟩

/-- A unit multiple of a free generator is a free generator. -/
lemma units_smul (he : IsFreeGenerator e) (g : Γ(X, U)ˣ) :
    IsFreeGenerator ((g : Γ(X, U)) • e) := by
  intro V h
  have : (fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE h).op ((g : Γ(X, U)) • e)) =
      (fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE h).op e) ∘
        (fun a ↦ a * X.presheaf.map (homOfLE h).op (g : Γ(X, U))) := by
    ext a
    simp [mul_smul]
  rw [this]
  exact (he V h).comp
    (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom g).mulRight_bijective

/-- The coefficient of a section `m` with respect to a free generator `e`: the unique `a` with
`a • e = m`. -/
noncomputable def coeff (he : IsFreeGenerator e) (m : Γ(M, U)) : Γ(X, U) :=
  Function.surjInv he.bijective.2 m

variable (he : IsFreeGenerator e)
include he

@[simp]
lemma coeff_smul (m : Γ(M, U)) : he.coeff m • e = m :=
  Function.surjInv_eq he.bijective.2 m

lemma coeff_eq_iff (m : Γ(M, U)) (a : Γ(X, U)) : he.coeff m = a ↔ a • e = m :=
  ⟨fun h ↦ h ▸ he.coeff_smul m, fun h ↦ he.bijective.1 ((he.coeff_smul m).trans h.symm)⟩

@[simp]
lemma coeff_smul_self (a : Γ(X, U)) : he.coeff (a • e) = a :=
  (he.coeff_eq_iff _ _).2 rfl

@[simp]
lemma coeff_add (m m' : Γ(M, U)) : he.coeff (m + m') = he.coeff m + he.coeff m' := by
  rw [coeff_eq_iff, add_smul, coeff_smul, coeff_smul]

@[simp]
lemma coeff_zero : he.coeff 0 = 0 := by
  rw [coeff_eq_iff, zero_smul]

@[simp]
lemma coeff_smul_left (a : Γ(X, U)) (m : Γ(M, U)) : he.coeff (a • m) = a * he.coeff m := by
  rw [coeff_eq_iff, mul_smul, coeff_smul]

lemma coeff_map {V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    (he.map h).coeff (M.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (he.coeff m) := by
  rw [coeff_eq_iff, ← map_smul, coeff_smul]

end IsFreeGenerator

/-- **Being a free generator is a local property.** A section which is a free generator on each
member of a covering sieve is a free generator. -/
lemma isFreeGenerator_of_mem {U : X.Opens} (e : Γ(M, U)) {S : Sieve U}
    (hS : S ∈ Opens.grothendieckTopology X U)
    (h : ∀ ⦃V : X.Opens⦄ (i : V ⟶ U), S i → IsFreeGenerator (M.presheaf.map i.op e)) :
    IsFreeGenerator e := by
  intro W hW
  have hS' := (Opens.grothendieckTopology X).pullback_stable (homOfLE hW) hS
  have hO := X.isSheaf_presheaf_comp_forget _ hS'
  have hM := isSheaf_presheaf_comp_forget M _ hS'
  refine ⟨fun a b hab ↦ ?_, fun m ↦ ?_⟩
  · refine hO.isSeparatedFor.ext fun V f hf ↦ (h _ hf).smul_left_injective ?_
    have := congr_arg (M.presheaf.map f.op) hab
    simp only [map_smul, presheaf_map_map_apply] at this
    exact this
  · let x : Presieve.FamilyOfElements (X.presheaf ⋙ CategoryTheory.forget CommRingCat)
        (S.pullback (homOfLE hW)).arrows := fun V f hf ↦
      ((h _ hf).coeff (M.presheaf.map f.op m) : Γ(X, V))
    have hx : x.Compatible := by
      intro Z₁ Z₂ V g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
      change X.presheaf.map g₁.op (x f₁ hf₁) = X.presheaf.map g₂.op (x f₂ hf₂)
      simp only [x]
      rw [← homOfLE_leOfHom g₁, ← homOfLE_leOfHom g₂, ← IsFreeGenerator.coeff_map,
        ← IsFreeGenerator.coeff_map]
      simp only [homOfLE_leOfHom, presheaf_map_map_apply]
      congr 2
    refine ⟨hO.amalgamate x hx, hM.isSeparatedFor.ext fun V f hf ↦ ?_⟩
    change M.presheaf.map f.op (_ • _) = _
    rw [map_smul, presheaf_map_map_apply]
    have := hO.valid_glue hx f hf
    change X.presheaf.map f.op _ = _ at this
    rw [this]
    exact (h _ hf).coeff_smul _

/-- If `M` is trivial on `U`, i.e. `M.over U ≅ 𝒪_U`, then `M` has a free generator on `U`,
namely the section corresponding to `1`. -/
lemma exists_isFreeGenerator_of_iso {U : X.Opens}
    (i : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ∃ e : Γ(M, U), IsFreeGenerator e := by
  let s := (M.over U).unitHomEquiv i.inv
  refine ⟨s.val (.op (Over.mk (𝟙 U))), fun V h ↦ ?_⟩
  let ψ := (i.inv.val.app (.op (Over.mk (homOfLE h)))).hom
  let ψ' : Γ(X, V) → Γ(M, V) := fun r ↦ ψ r
  have h1 (r : Γ(X, V)) : ψ' r = r • ψ' 1 :=
    (congrArg ψ (mul_one r).symm).trans (ψ.map_smul r (1 : Γ(X, V)))
  have h2 : M.presheaf.map (homOfLE h).op (s.val (.op (Over.mk (𝟙 U)))) = ψ' 1 :=
    s.2 (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op
  have key : (fun r : Γ(X, V) ↦ r • M.presheaf.map (homOfLE h).op
      (s.val (.op (Over.mk (𝟙 U))))) = ψ' := by
    ext r
    rw [h1, h2]
  rw [key]
  exact ConcreteCategory.bijective_of_isIso ((PresheafOfModules.evaluation _
    (.op (Over.mk (homOfLE h)))).mapIso ((SheafOfModules.forget _).mapIso i)).inv

/-- **Invertible modules are locally trivial.** Every point `x` of an open `W` has an affine
open neighbourhood `U ⊆ W` on which an invertible module has a free generator. -/
lemma exists_isFreeGenerator (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] {x : X}
    {W : X.Opens} (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧ ∃ e : Γ(M, U.1), IsFreeGenerator e := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsInvertible.exists_isInvertibleData (M := M)
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).mp q.coversTop).exists_mem x
  obtain ⟨hu⟩ := SheafOfModules.LocalGeneratorsData.IsInvertibleData.nonempty_unique (q := q) i
  have := SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i
  obtain ⟨e, he⟩ := exists_isFreeGenerator_of_iso
    ((asIso (q.generators i).π).symm ≪≫ SheafOfModules.freeUniqueIso _)
  obtain ⟨V, hV, hxV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := q.X i ⊓ W) ⟨hi, hx⟩
  have hVi : V ≤ q.X i := fun y hy ↦ (hVW hy).1
  exact ⟨⟨V, hV⟩, hxV, fun y hy ↦ (hVW hy).2, _, he.map hVi⟩

/-- An isomorphism of modules carries free generators to free generators. -/
lemma IsFreeGenerator.app_hom {M' : X.Modules} (e : M ≅ M') {U : X.Opens} {x : Γ(M, U)}
    (hx : IsFreeGenerator x) : IsFreeGenerator (e.hom.app U x) := by
  intro V h
  have he : Function.Bijective (e.hom.app V) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨e.inv.app V, fun y ↦ ?_, fun y ↦ ?_⟩
    · change (e.hom.app V ≫ e.inv.app V) y = y
      rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app]
      rfl
    · change (e.inv.app V ≫ e.hom.app V) y = y
      rw [← Hom.comp_app, e.inv_hom_id, Hom.id_app]
      rfl
  convert he.comp (hx V h) using 1
  ext r
  simp only [Function.comp_apply, Hom.app_smul, Hom.app_presheaf_map]

/-- A free generator `e` of `M` over `U` trivializes `M` over `U`: `a ↦ a • e` is an isomorphism
`𝒪_U ≅ M|_U`. -/
noncomputable def IsFreeGenerator.overIso {U : X.Opens} {e : Γ(M, U)} (he : IsFreeGenerator e) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  let σ : (M.over U).sections := PresheafOfModules.sectionsMk
    (fun W ↦ show Γ(M, W.unop.left) from M.presheaf.map W.unop.hom.op e)
    (fun W W' f ↦ by
      change M.presheaf.map f.unop.left.op (M.presheaf.map W.unop.hom.op e) = _
      rw [presheaf_map_map_apply]
      rfl)
  let φ := (M.over U).unitHomEquiv.symm σ
  have : IsIso φ := by
    have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map φ) := by
      refine (NatTrans.isIso_iff_isIso_app _).2 fun W ↦ ?_
      rw [ConcreteCategory.isIso_iff_bijective]
      exact he _ (leOfHom W.unop.hom)
    exact isIso_of_reflects_iso φ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
  (asIso φ).symm

/-- The image of a free generator under a morphism which is bijective on all sections over
opens `V ⊆ U` is a free generator. -/
lemma IsFreeGenerator.app_of_bijective (φ : M ⟶ N) {U : X.Opens} {e : Γ(M, U)}
    (he : IsFreeGenerator e) (hφ : ∀ V ≤ U, Function.Bijective (φ.app V)) :
    IsFreeGenerator (φ.app U e) := by
  intro V h
  have : (fun r : Γ(X, V) ↦ r • N.presheaf.map (homOfLE h).op (φ.app U e)) =
      φ.app V ∘ fun r : Γ(X, V) ↦ r • M.presheaf.map (homOfLE h).op e := by
    funext r
    simp [Hom.app_smul, Hom.app_presheaf_map]
  rw [this]
  exact (hφ V h).comp (he V h)

/-- The section `1` is a free generator of the structure sheaf on every open. -/
lemma isFreeGenerator_one (U : X.Opens) :
    IsFreeGenerator (M := Modules.unit X) (U := U) (1 : Γ(X, U)) := by
  intro V h
  have key (r : Γ(X, V)) : r • (Modules.unit X).presheaf.map
      (homOfLE h).op (1 : Γ(X, U)) = r :=
    (congrArg (r * ·) (map_one (X.presheaf.map (homOfLE h).op).hom)).trans (mul_one r)
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ⟨b, key b⟩⟩
  exact (key a).symm.trans (hab.trans (key b))

end Modules

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Restricting a section of `M` twice along inclusions of opens. -/
lemma presheaf_map_homOfLE_map_homOfLE {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V)
    (e : Γ(M, U)) :
    M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE h).op e) =
      M.presheaf.map (homOfLE (h'.trans h)).op e :=
  presheaf_map_map_apply _ _ _

/-- A relation `m = ρ • m'` over `V` restricts to the relation `m = ρ|_W • m'` over `W ⊆ V`. -/
lemma presheaf_map_homOfLE_eq_smul {U V W : X.Opens} (h : V ≤ U) (hW : W ≤ V)
    {m m' : Γ(M, U)} {ρ : Γ(X, V)}
    (H : M.presheaf.map (homOfLE h).op m = ρ • M.presheaf.map (homOfLE h).op m') :
    M.presheaf.map (homOfLE (hW.trans h)).op m =
      X.presheaf.map (homOfLE hW).op ρ • M.presheaf.map (homOfLE (hW.trans h)).op m' := by
  rw [← presheaf_map_homOfLE_map_homOfLE h hW, H, map_smul, presheaf_map_homOfLE_map_homOfLE]

/-- **A criterion for a free generator.** A section `σ` of `Q` over `U` such that multiplication
`r ↦ r • σ` is injective over every open of `U`, and every section over an open of `U` is
locally a multiple of `σ`, is a free generator. -/
lemma isFreeGenerator_of_locally {Q : X.Modules} {U : X.Opens} (σ : Γ(Q, U))
    (hinj : ∀ (V : X.Opens) (h : V ≤ U),
      Function.Injective fun r : Γ(X, V) ↦ r • Q.presheaf.map (homOfLE h).op σ)
    (hsurj : ∀ (V : X.Opens) (h : V ≤ U) (q : Γ(Q, V)), ∃ S : Sieve V,
      S ∈ Opens.grothendieckTopology X V ∧ ∀ ⦃W : X.Opens⦄ (i : W ⟶ V), S i →
        ∃ a : Γ(X, W), Q.presheaf.map i.op q =
          a • Q.presheaf.map (homOfLE ((leOfHom i).trans h)).op σ) :
    IsFreeGenerator σ := by
  intro V h
  refine ⟨hinj V h, fun q ↦ ?_⟩
  obtain ⟨S, hS, hq⟩ := hsurj V h q
  have hO := X.isSheaf_presheaf_comp_forget _ hS
  have hQ := isSheaf_presheaf_comp_forget Q _ hS
  choose a ha using hq
  let x : Presieve.FamilyOfElements (X.presheaf ⋙ CategoryTheory.forget CommRingCat)
      S.arrows := fun W i hi ↦ (a i hi : Γ(X, W))
  have hσ (W : X.Opens) (k k' : W ⟶ U) : Q.presheaf.map k.op σ = Q.presheaf.map k'.op σ := by
    rw [Subsingleton.elim k k']
  have hx : x.Compatible := by
    intro Z₁ Z₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    change X.presheaf.map g₁.op (a f₁ hf₁) = X.presheaf.map g₂.op (a f₂ hf₂)
    refine hinj W ((leOfHom (g₁ ≫ f₁)).trans h) ?_
    have e₁ := congrArg (Q.presheaf.map g₁.op) (ha f₁ hf₁)
    have e₂ := congrArg (Q.presheaf.map g₂.op) (ha f₂ hf₂)
    rw [map_smul, presheaf_map_map_apply, presheaf_map_map_apply] at e₁ e₂
    rw [hcomm] at e₁
    dsimp only
    rw [hσ W (g₂ ≫ homOfLE ((leOfHom f₂).trans h)) (g₁ ≫ homOfLE ((leOfHom f₁).trans h))]
      at e₂
    rw [hσ W (homOfLE _) (g₁ ≫ homOfLE ((leOfHom f₁).trans h))]
    exact e₁.symm.trans e₂
  refine ⟨hO.amalgamate x hx, hQ.isSeparatedFor.ext fun W i hi ↦ ?_⟩
  refine Eq.trans ?_ (ha i hi).symm
  change Q.presheaf.map i.op (_ • _) = _
  rw [map_smul, presheaf_map_map_apply,
    hσ W (i ≫ homOfLE h) (homOfLE ((leOfHom i).trans h))]
  congr 1
  exact hO.valid_glue hx i hi

section Glue

variable {ι : Type*} {U : ι → X.Opens} (e : ∀ i, Γ(M, U i)) (f : ∀ i, Γ(N, U i))

/-- `n` is the value at `m` of the morphism `M ⟶ N` sending each `e i` to `f i`: whenever
`m = a • e i` on an open `W`, then `n = a • f i` on `W`. -/
def IsGlueValue {V : X.Opens} (m : Γ(M, V)) (n : Γ(N, V)) : Prop :=
  ∀ i (W : X.Opens) (hW : W ≤ V) (hWi : W ≤ U i) (a : Γ(X, W)),
    a • M.presheaf.map (homOfLE hWi).op (e i) = M.presheaf.map (homOfLE hW).op m →
      N.presheaf.map (homOfLE hW).op n = a • N.presheaf.map (homOfLE hWi).op (f i)

variable {e f}

lemma IsGlueValue.unique (hU : ⨆ i, U i = ⊤) (he : ∀ i, IsFreeGenerator (e i)) {V : X.Opens}
    {m : Γ(M, V)} {n n' : Γ(N, V)} (hn : IsGlueValue e f m n) (hn' : IsGlueValue e f m n') :
    n = n' := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun i ↦ V ⊓ U i) V
    (fun _ ↦ homOfLE inf_le_left) (fun x hx ↦ ?_) n n' fun i ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · have hi := (he i).map (inf_le_right : V ⊓ U i ≤ U i)
    have ha := hi.coeff_smul (M.presheaf.map (homOfLE inf_le_left).op m)
    exact (hn i _ inf_le_left inf_le_right _ ha).trans (hn' i _ inf_le_left inf_le_right _ ha).symm

variable (hU : ⨆ i, U i = ⊤) (he : ∀ i, IsFreeGenerator (e i))
  (hc : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W)),
    a • M.presheaf.map (homOfLE hi).op (e i) = b • M.presheaf.map (homOfLE hj).op (e j) →
      a • N.presheaf.map (homOfLE hi).op (f i) = b • N.presheaf.map (homOfLE hj).op (f j))

include hU he hc in
lemma exists_isGlueValue {V : X.Opens} (m : Γ(M, V)) : ∃ n, IsGlueValue e f m n := by
  have hi (i : ι) := (he i).map (inf_le_right : V ⊓ U i ≤ U i)
  let sf (i : ι) : Γ(N, V ⊓ U i) := (hi i).coeff (M.presheaf.map (homOfLE inf_le_left).op m) •
    N.presheaf.map (homOfLE inf_le_right).op (f i)
  have hsf : TopCat.Presheaf.IsCompatible N.presheaf (fun i ↦ V ⊓ U i) sf := by
    intro i j
    change N.presheaf.map (homOfLE inf_le_left).op (sf i) =
      N.presheaf.map (homOfLE inf_le_right).op (sf j)
    simp only [sf, map_smul, presheaf_map_homOfLE_map_homOfLE]
    refine hc i j _ _ _ _ _ ?_
    rw [← presheaf_map_homOfLE_map_homOfLE (inf_le_right : V ⊓ U i ≤ U i) inf_le_left,
      ← presheaf_map_homOfLE_map_homOfLE (inf_le_right : V ⊓ U j ≤ U j) inf_le_right,
      ← map_smul, ← map_smul, (hi i).coeff_smul, (hi j).coeff_smul,
      presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE]
  obtain ⟨n, hn, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ U i) V (fun _ ↦ homOfLE inf_le_left) (fun x hx ↦ by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
      exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩) sf hsf
  refine ⟨n, fun i W hW hWi a ha ↦ ?_⟩
  have hWV : W ≤ V ⊓ U i := le_inf hW hWi
  have h1 : N.presheaf.map (homOfLE hW).op n =
      N.presheaf.map (homOfLE hWV).op (N.presheaf.map (homOfLE inf_le_left).op n) :=
    (presheaf_map_homOfLE_map_homOfLE _ _ _).symm
  rw [h1, hn i]
  simp only [sf, map_smul, presheaf_map_homOfLE_map_homOfLE]
  congr 1
  refine ((he i).map hWi).smul_left_injective ?_
  dsimp only
  rw [ha, ← presheaf_map_homOfLE_map_homOfLE (inf_le_right : V ⊓ U i ≤ U i) hWV, ← map_smul,
    (hi i).coeff_smul, presheaf_map_homOfLE_map_homOfLE]


include he in
lemma isGlueValue_zero {V : X.Opens} : IsGlueValue e f (0 : Γ(M, V)) (0 : Γ(N, V)) := by
  intro i W hW hWi a ha
  rw [map_zero] at ha ⊢
  obtain rfl : a = 0 := ((he i).map hWi).smul_left_injective (ha.trans (zero_smul _ _).symm)
  rw [zero_smul]

include he in
lemma IsGlueValue.add {V : X.Opens} {m m' : Γ(M, V)} {n n' : Γ(N, V)}
    (hn : IsGlueValue e f m n) (hn' : IsGlueValue e f m' n') :
    IsGlueValue e f (m + m') (n + n') := by
  intro i W hW hWi a ha
  have hi := (he i).map hWi
  have h1 := hn i W hW hWi _ (hi.coeff_smul (M.presheaf.map (homOfLE hW).op m))
  have h2 := hn' i W hW hWi _ (hi.coeff_smul (M.presheaf.map (homOfLE hW).op m'))
  rw [map_add] at ha ⊢
  rw [h1, h2, ← add_smul]
  congr 1
  rw [← hi.coeff_add, ← ha, hi.coeff_smul_self]

include he in
lemma IsGlueValue.smul {V : X.Opens} {m : Γ(M, V)} {n : Γ(N, V)} (hn : IsGlueValue e f m n)
    (r : Γ(X, V)) : IsGlueValue e f (r • m) (r • n) := by
  intro i W hW hWi a ha
  have hi := (he i).map hWi
  have h1 := hn i W hW hWi _ (hi.coeff_smul (M.presheaf.map (homOfLE hW).op m))
  rw [map_smul] at ha ⊢
  rw [h1, smul_smul]
  congr 1
  rw [← hi.coeff_smul_left, ← ha, hi.coeff_smul_self]

lemma IsGlueValue.map {V V' : X.Opens} (h : V' ≤ V) {m : Γ(M, V)} {n : Γ(N, V)}
    (hn : IsGlueValue e f m n) :
    IsGlueValue e f (M.presheaf.map (homOfLE h).op m) (N.presheaf.map (homOfLE h).op n) := by
  intro i W hW hWi a ha
  rw [presheaf_map_homOfLE_map_homOfLE] at ha ⊢
  exact hn i W _ hWi a ha

include he in
lemma IsGlueValue.symm (hf : ∀ i, IsFreeGenerator (f i)) {V : X.Opens} {m : Γ(M, V)}
    {n : Γ(N, V)} (hn : IsGlueValue e f m n) : IsGlueValue f e n m := by
  intro i W hW hWi a ha
  have hi := (he i).map hWi
  have h1 := hn i W hW hWi _ (hi.coeff_smul (M.presheaf.map (homOfLE hW).op m))
  rw [← hi.coeff_smul (M.presheaf.map (homOfLE hW).op m)]
  congr 1
  exact ((hf i).map hWi).smul_left_injective (h1.symm.trans ha.symm)

include hU he hc in
/-- The morphism `M ⟶ N` sending the free generators `e i` to the sections `f i`. -/
noncomputable def glueHom : M ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun m := (exists_isGlueValue hU he hc (V := V.unop) m).choose
          map_zero' := ((exists_isGlueValue hU he hc _).choose_spec).unique hU he
            (isGlueValue_zero he)
          map_add' m m' := ((exists_isGlueValue hU he hc _).choose_spec).unique hU he
            (((exists_isGlueValue hU he hc m).choose_spec).add he
              (exists_isGlueValue hU he hc m').choose_spec) }
      naturality V V' i := by
        ext m
        exact ((exists_isGlueValue hU he hc _).choose_spec).unique hU he
          (((exists_isGlueValue hU he hc m).choose_spec).map (V' := V'.unop) i.unop.le) }
    fun V r m ↦ ((exists_isGlueValue hU he hc _).choose_spec).unique hU he
      (((exists_isGlueValue hU he hc m).choose_spec).smul he r)⟩

lemma isGlueValue_glueHom_app {V : X.Opens} (m : Γ(M, V)) :
    IsGlueValue e f m ((glueHom hU he hc).app V m) :=
  (exists_isGlueValue hU he hc m).choose_spec


include hU he hc in
/-- **Invertible modules with the same transition functions are isomorphic.** Let `U i` be an
open cover of `X`, `e i` a free generator of `M` on `U i` and `f i` a free generator of `N` on
`U i`, such that `e i` and `e j` are related on every open of `U i ⊓ U j` in the same way as
`f i` and `f j` (i.e. both families have the same transition functions). Then `M ≅ N`. -/
theorem nonempty_iso_of_isFreeGenerator (hf : ∀ i, IsFreeGenerator (f i)) :
    Nonempty (M ≅ N) := by
  have hc' : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W)),
      a • N.presheaf.map (homOfLE hi).op (f i) = b • N.presheaf.map (homOfLE hj).op (f j) →
        a • M.presheaf.map (homOfLE hi).op (e i) = b • M.presheaf.map (homOfLE hj).op (e j) := by
    intro i j W hi hj a b hab
    have hj' := (he j).map hj
    have h := hc i j W hi hj a _ (hj'.coeff_smul _).symm
    rw [← hj'.coeff_smul (a • M.presheaf.map (homOfLE hi).op (e i))]
    congr 1
    exact ((hf j).map hj).smul_left_injective (h.symm.trans hab)
  refine ⟨⟨glueHom hU he hc, glueHom hU hf hc', ?_, ?_⟩⟩
  · refine hom_ext _ _ fun V ↦ ?_
    ext m
    exact (isGlueValue_glueHom_app hU hf hc' _).unique hU hf
      ((isGlueValue_glueHom_app hU he hc m).symm he hf)
  · refine hom_ext _ _ fun V ↦ ?_
    ext m
    exact (isGlueValue_glueHom_app hU he hc _).unique hU he
      ((isGlueValue_glueHom_app hU hf hc' m).symm hf he)

end Glue

variable {Y : Scheme.{u}}

/-- A morphism `φ : 𝒪_X ⟶ M` which is an isomorphism over an open `U` gives a free generator of
`M` on `U`, namely the restriction of `φ 1`. -/
lemma isFreeGenerator_of_isIso_restrict (φ : Modules.unit X ⟶ M)
    {U : X.Opens} [IsIso ((restrictFunctor U.ι).map φ)] :
    IsFreeGenerator (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (Hom.app φ ⊤ (1 : Γ(X, ⊤)))) := by
  intro V hV
  obtain ⟨V', rfl⟩ : ∃ V' : U.toScheme.Opens, U.ι ''ᵁ V' = V :=
    ⟨U.ι ⁻¹ᵁ V, by rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.2 hV]⟩
  have key : (fun r : Γ(X, U.ι ''ᵁ V') ↦ r • M.presheaf.map (homOfLE hV).op
      (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (Hom.app φ ⊤ (1 : Γ(X, ⊤))))) =
      Hom.app φ (U.ι ''ᵁ V') := by
    funext r
    rw [presheaf_map_homOfLE_map_homOfLE]
    erw [← Hom.app_presheaf_map, ← Hom.app_smul]
    congr 1
    change r * X.presheaf.map _ 1 = r
    rw [map_one]
    exact mul_one r
  rw [key]
  exact ConcreteCategory.bijective_of_isIso (((restrictFunctor U.ι).map φ).app V')


section Pullback

variable (g : X ⟶ Y)

/-- If `φ` is an isomorphism over an open `U`, then its pullback along `g` is an isomorphism over
`g⁻¹ U`. -/
lemma isIso_restrictFunctor_map_pullback_map {M N : Y.Modules} (φ : M ⟶ N) {U : Y.Opens}
    [IsIso ((restrictFunctor U.ι).map φ)] :
    IsIso ((restrictFunctor (g ⁻¹ᵁ U).ι).map ((pullback g).map φ)) := by
  rw [NatIso.isIso_map_iff (restrictFunctorIsoPullback (g ⁻¹ᵁ U).ι)]
  have : IsIso ((pullback U.ι).map φ) := by
    rw [← NatIso.isIso_map_iff (restrictFunctorIsoPullback U.ι)]
    infer_instance
  have e : pullback g ⋙ pullback (g ⁻¹ᵁ U).ι ≅ pullback U.ι ⋙ pullback (g ∣_ U) :=
    pullbackComp _ _ ≪≫ pullbackCongr (morphismRestrict_ι g U).symm ≪≫ (pullbackComp _ _).symm
  exact (NatIso.isIso_map_iff e φ).2
    (inferInstanceAs (IsIso ((pullback (g ∣_ U)).map ((pullback U.ι).map φ))))

/-- The pullback `g^* m` of a section `m` of an `𝒪_Y`-module `M` over `U`, a section of `g^* M`
over `g⁻¹ U`: the image of `m` under the unit `M ⟶ g_* g^* M`. -/
noncomputable def pullbackSection {M : Y.Modules} {U : Y.Opens} (m : Γ(M, U)) :
    Γ((pullback g).obj M, g ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction g).unit.app M).app U m

lemma pullbackSection_add {M : Y.Modules} {U : Y.Opens} (m m' : Γ(M, U)) :
    pullbackSection g (m + m') = pullbackSection g m + pullbackSection g m' :=
  map_add _ _ _

lemma pullbackSection_smul {M : Y.Modules} {U : Y.Opens} (r : Γ(Y, U)) (m : Γ(M, U)) :
    pullbackSection g (r • m) = g.app U r • pullbackSection g m :=
  Hom.app_smul _ r m

lemma pullbackSection_map {M : Y.Modules} {U V : Y.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    pullbackSection g (M.presheaf.map (homOfLE h).op m) =
      ((pullback g).obj M).presheaf.map (homOfLE (g.preimage_mono h)).op
        (pullbackSection g m) :=
  Hom.app_presheaf_map _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback of the section `φ 1` attached to a morphism `φ : 𝒪_Y ⟶ M` is the section
attached to the pullback `𝒪_X ≅ g^* 𝒪_Y ⟶ g^* M` of `φ`. -/
lemma pullbackSection_app_one {M : Y.Modules} (φ : Modules.unit Y ⟶ M) :
    pullbackSection g (Hom.app φ ⊤ (1 : Γ(Y, ⊤))) =
      Hom.app ((pullbackObjUnitIso g).inv ≫ (pullback g).map φ) (g ⁻¹ᵁ ⊤) (1 : Γ(X, ⊤)) := by
  have h1 := (pullbackPushforwardAdjunction g).unit.naturality φ
  have h2 : (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackObjUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [Adjunction.homEquiv_unit] at h2
  have h3 := congrArg (fun ψ : Modules.unit Y ⟶ (pushforward g).obj (Modules.unit X) ↦
    (Hom.app ψ ⊤) (1 : Γ(Y, ⊤))) h2
  have h1' := congrArg (fun ψ : Modules.unit Y ⟶ (pushforward g).obj ((pullback g).obj M) ↦
    (Hom.app ψ ⊤) (1 : Γ(Y, ⊤))) h1
  have e1 : (Hom.app (SheafOfModules.unitToPushforwardObjUnit (Hom.toRingCatSheafHom g)) ⊤)
      (1 : Γ(Y, ⊤)) = (1 : Γ(X, ⊤)) :=
    map_one g.appTop.hom
  dsimp only at h1' h3
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply, Functor.id_map,
    Functor.comp_map] at h1' h3
  have h4 : (Hom.app ((pullbackPushforwardAdjunction g).unit.app (Modules.unit Y)) ⊤)
      (1 : Γ(Y, ⊤)) = Hom.app (pullbackObjUnitIso g).inv (g ⁻¹ᵁ ⊤) (1 : Γ(X, ⊤)) := by
    have h5 (x : Γ((pullback g).obj (Modules.unit Y), g ⁻¹ᵁ ⊤)) :
        Hom.app (pullbackObjUnitIso g).inv (g ⁻¹ᵁ ⊤)
          (Hom.app (pullbackObjUnitIso g).hom (g ⁻¹ᵁ ⊤) x) = x := by
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
      rfl
    exact (h5 _).symm.trans (congrArg (Hom.app (pullbackObjUnitIso g).inv (g ⁻¹ᵁ ⊤))
      (h3.trans e1))
  exact h1'.trans (congrArg (Hom.app ((pullback g).map φ) (g ⁻¹ᵁ ⊤)) h4)

variable {g} in
/-- If `φ : 𝒪_Y ⟶ M` is an isomorphism over an open `U`, then so is the composite
`𝒪_X ≅ g^* 𝒪_Y ⟶ g^* M` over `g⁻¹ U`. -/
lemma isIso_restrictFunctor_map_pullbackObjUnitIso_inv_comp {M : Y.Modules}
    (φ : Modules.unit Y ⟶ M) {U : Y.Opens} [IsIso ((restrictFunctor U.ι).map φ)] :
    IsIso ((restrictFunctor (g ⁻¹ᵁ U).ι).map
      ((pullbackObjUnitIso g).inv ≫ (pullback g).map φ)) := by
  have := isIso_restrictFunctor_map_pullback_map g φ (U := U)
  have h0 : IsIso ((restrictFunctor (g ⁻¹ᵁ U).ι).map (pullbackObjUnitIso g).inv) :=
    ((restrictFunctor _).mapIso (pullbackObjUnitIso g).symm).isIso_hom
  erw [Functor.map_comp]
  exact IsIso.comp_isIso

variable {g} in
/-- If `φ : 𝒪_Y ⟶ M` is an isomorphism over an open `U`, the pullback along `g` of the section
`φ 1` is a free generator of `g^* M` over `g⁻¹ U`. -/
lemma isFreeGenerator_pullbackSection {M : Y.Modules} (φ : Modules.unit Y ⟶ M) {U : Y.Opens}
    [IsIso ((restrictFunctor U.ι).map φ)] :
    IsFreeGenerator (((pullback g).obj M).presheaf.map
      (homOfLE (g.preimage_mono (le_top : U ≤ ⊤))).op
      (pullbackSection g (Hom.app φ ⊤ (1 : Γ(Y, ⊤))))) := by
  have := isIso_restrictFunctor_map_pullbackObjUnitIso_inv_comp φ (g := g) (U := U)
  rw [pullbackSection_app_one]
  exact isFreeGenerator_of_isIso_restrict (U := g ⁻¹ᵁ U) _

/-- A relation `m = ρ • m'` over `V` between sections of `M` pulls back to the relation
`g^* m = g^♯ ρ • g^* m'` over `g⁻¹ V`. -/
lemma pullbackSection_map_eq_smul {M : Y.Modules} {U V : Y.Opens} (h : V ≤ U)
    {m m' : Γ(M, U)} {ρ : Γ(Y, V)}
    (H : M.presheaf.map (homOfLE h).op m = ρ • M.presheaf.map (homOfLE h).op m') :
    ((pullback g).obj M).presheaf.map (homOfLE (g.preimage_mono h)).op (pullbackSection g m) =
      g.app V ρ • ((pullback g).obj M).presheaf.map (homOfLE (g.preimage_mono h)).op
        (pullbackSection g m') := by
  rw [← pullbackSection_map g h, ← pullbackSection_map g h, H, pullbackSection_smul]

end Pullback

end AlgebraicGeometry.Scheme.Modules
