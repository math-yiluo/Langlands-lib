import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensor
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Tensor products of line bundles glued from unit cocycles

For unit families `g` and `h` on the overlaps of opens `T i`, multiplying the components of a
section of `glued g` and a section of `glued h` gives a section of `glued (g * h)`. This
bilinear map defines a morphism `mulHom g h : tensorObj (glued g) (glued h) ⟶ glued (g * h)`
out of the sheaf tensor product. When `g` and `h` are cocycles and the `T i` cover `X`, it is an
isomorphism `tensorIso`, which sends the tensor of the local generators `genSec g i` and
`genSec h i` to the local generator `genSec (g * h) i`.

The isomorphism criterion `isIso_of_bijective_tensorHomEquiv` applies to any morphism out of a
sheaf tensor product whose sectionwise tensor adjoint is bijective over the opens inside the
members of a cover.
-/

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

variable {X : Scheme.{u}}

section Criterion

/-- The image of the sectionwise tensor `m ⊗ n` in the sheaf tensor product. -/
noncomputable def tmulSec {M N : X.Modules} {U : X.Opens} (m : Γ(M, U)) (n : Γ(N, U)) :
    Γ(tensorObj M N, U) :=
  ((tensorSheafifyUnit M N).app (op U)).hom (m ⊗ₜ n)

/-- `tmulSec` commutes with restriction. -/
lemma map_tmulSec {M N : X.Modules} {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    (tensorObj M N).presheaf.map i.op (tmulSec m n) =
      tmulSec (M.presheaf.map i.op m) (N.presheaf.map i.op n) :=
  (PresheafOfModules.naturality_apply (tensorSheafifyUnit M N) i.op (m ⊗ₜ n)).symm

/-- A morphism out of the sheaf tensor product evaluated on `tmulSec m n` is its sectionwise
tensor adjoint evaluated on `m ⊗ n`. -/
lemma app_tmulSec {M N P : X.Modules} (φ : tensorObj M N ⟶ P) {U : X.Opens} (m : Γ(M, U))
    (n : Γ(N, U)) :
    φ.app U (tmulSec m n) = ((tensorHomEquiv M N P φ).app (op U)).hom (m ⊗ₜ n) := by
  rw [show tensorHomEquiv M N P φ = tensorSheafifyUnit M N ≫ φ.val from
    (sheafifyAdjunction X).homEquiv_unit _ _ _]
  rfl

/-- A morphism out of the sheaf tensor product is an isomorphism if its sectionwise tensor
adjoint is bijective over every open contained in a member of an open cover. -/
lemma isIso_of_bijective_tensorHomEquiv {M N P : X.Modules} (φ : tensorObj M N ⟶ P)
    {κ : Type*} (T : κ → X.Opens) (hT : (⨆ i, T i) = ⊤)
    (hφ : ∀ (i : κ) (V : X.Opens), V ≤ T i →
      Function.Bijective ((tensorHomEquiv M N P φ).app (op V)).hom) : IsIso φ := by
  have hloc : ∀ (U : X.Opens) (x : X), x ∈ U → ∃ (V : X.Opens) (j : V ⟶ U), x ∈ V ∧
      Function.Bijective ((tensorHomEquiv M N P φ).app (op V)).hom := by
    intro U x hx
    have hx' : x ∈ (⨆ i, T i) := by
      rw [hT]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
    exact ⟨U ⊓ T i, homOfLE inf_le_left, ⟨hx, hi⟩, hφ i _ inf_le_right⟩
  let f₁ := (PresheafOfModules.toPresheaf _).map (tensorSheafifyUnit M N)
  let f₂ := (PresheafOfModules.toPresheaf _).map φ.val
  let f₃ := (PresheafOfModules.toPresheaf _).map (tensorHomEquiv M N P φ)
  have fac : f₁ ≫ f₂ = f₃ := by
    simp only [f₁, f₂, f₃]
    rw [← Functor.map_comp]
    congr 1
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f₁ :=
    (inferInstance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (M.val ⊗ N.val).presheaf))
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f₃ := by
    constructor
    intro U s
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, j, hxV, hbij⟩ := hloc U x hx
    refine ⟨V, j, ?_, hxV⟩
    rw [Presheaf.imageSieve_apply]
    obtain ⟨y, hy⟩ := hbij.2 (((PresheafOfModules.toPresheaf _).obj P.val).map j.op s)
    exact ⟨y, hy⟩
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f₃ := by
    constructor
    intro U a b h
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, j, hxV, hbij⟩ := hloc U.unop x hx
    refine ⟨V, j, ?_, hxV⟩
    rw [Presheaf.equalizerSieve_apply]
    apply hbij.1
    exact (NatTrans.naturality_apply f₃ j.op a).trans
      ((congrArg _ h).trans (NatTrans.naturality_apply f₃ j.op b).symm)
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f₂ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ fac
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f₂ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ f₃ fac
  have : IsIso ((SheafOfModules.toSheaf _).map φ) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1
      ⟨inferInstanceAs (Presheaf.IsLocallyInjective _ f₂),
        inferInstanceAs (Presheaf.IsLocallySurjective _ f₂)⟩
  exact isIso_of_reflects_iso (C := SheafOfModules X.ringCatSheaf) φ
    (SheafOfModules.toSheaf X.ringCatSheaf)

end Criterion

variable {ι : Type u} {T : ι → X.Opens}

section Cocycle

variable {g h : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}

lemma mul_apply_val (i j : ι) :
    ((g * h) i j : Γ(X, T i ⊓ T j)) = (g i j : Γ(X, T i ⊓ T j)) * (h i j : Γ(X, T i ⊓ T j)) :=
  rfl

/-- The product of two unit cocycles is a unit cocycle. -/
lemma IsCocycle.mul (hg : IsCocycle g) (hh : IsCocycle h) : IsCocycle (g * h) := by
  intro i j k
  simp only [mul_apply_val, map_mul]
  rw [← hg i j k, ← hh i j k]
  ring

end Cocycle

section Mul

variable (g h : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)

lemma compat_mul {U : X.Opens} {b c : Fam T U} (hb : Compat g b) (hc : Compat h c) :
    Compat (g * h) (fun i ↦ b i * c i) := by
  intro i j V hi hj
  simp only [map_mul, hb i j V hi hj, hc i j V hi hj, mul_apply_val]
  ring

/-- The componentwise product of a section of `glued g` and a section of `glued h`. -/
noncomputable def mulSec {U : X.Opens} (m : Γ(glued g, U)) (n : Γ(glued h, U)) :
    Γ(glued (g * h), U) :=
  mk (g * h) (fun i ↦ comp g m i * comp h n i)
    (compat_mul g h (compat_of_mem g m) (compat_of_mem h n))

lemma comp_mulSec {U : X.Opens} (m : Γ(glued g, U)) (n : Γ(glued h, U)) (i : ι) :
    comp (g * h) (mulSec g h m n) i = comp g m i * comp h n i :=
  rfl

lemma mulSec_add_left {U : X.Opens} (m m' : Γ(glued g, U)) (n : Γ(glued h, U)) :
    mulSec g h (m + m') n = mulSec g h m n + mulSec g h m' n :=
  eq_of_comp (g * h) fun i ↦ add_mul (comp g m i) (comp g m' i) (comp h n i)

lemma mulSec_add_right {U : X.Opens} (m : Γ(glued g, U)) (n n' : Γ(glued h, U)) :
    mulSec g h m (n + n') = mulSec g h m n + mulSec g h m n' :=
  eq_of_comp (g * h) fun i ↦ mul_add (comp g m i) (comp h n i) (comp h n' i)

lemma mulSec_smul_left {U : X.Opens} (r : Γ(X, U)) (m : Γ(glued g, U)) (n : Γ(glued h, U)) :
    mulSec g h (r • m) n = r • mulSec g h m n :=
  eq_of_comp (g * h) fun i ↦ mul_assoc
    (X.presheaf.map (homOfLE inf_le_left : U ⊓ T i ⟶ U).op r) (comp g m i) (comp h n i)

lemma mulSec_smul_right {U : X.Opens} (r : Γ(X, U)) (m : Γ(glued g, U)) (n : Γ(glued h, U)) :
    mulSec g h m (r • n) = r • mulSec g h m n :=
  eq_of_comp (g * h) fun i ↦ mul_left_comm (comp g m i)
    (X.presheaf.map (homOfLE inf_le_left : U ⊓ T i ⟶ U).op r) (comp h n i)

/-- `mulSec` commutes with restriction. -/
lemma map_mulSec {U V : X.Opens} (f : V ⟶ U) (m : Γ(glued g, U)) (n : Γ(glued h, U)) :
    (glued (g * h)).presheaf.map f.op (mulSec g h m n) =
      mulSec g h ((glued g).presheaf.map f.op m) ((glued h).presheaf.map f.op n) :=
  eq_of_comp (g * h) fun i ↦ map_mul (X.presheaf.map
    (homOfLE (inf_le_inf_right (T i) (leOfHom f))).op).hom (comp g m i) (comp h n i)

/-- The product of the local generators of `glued g` and `glued h` is the local generator of
`glued (g * h)`. -/
lemma mulSec_genSec (hg : IsCocycle g) (hh : IsCocycle h) (i : ι) {V : X.Opens}
    (hV : V ≤ T i) :
    mulSec g h (genSec g hg i hV) (genSec h hh i hV) = genSec (g * h) (hg.mul hh) i hV :=
  eq_of_comp (g * h) fun j ↦ (map_mul (X.presheaf.map (homOfLE (le_inf inf_le_right
    (inf_le_left.trans hV) : V ⊓ T j ≤ T j ⊓ T i)).op).hom (g j i : Γ(X, T j ⊓ T i))
    (h j i : Γ(X, T j ⊓ T i))).symm

/-- `mulSec` as a bilinear map over `Γ(X, U)`. -/
noncomputable def mulBilin (U : X.Opens) :
    Γ(glued g, U) →ₗ[Γ(X, U)] Γ(glued h, U) →ₗ[Γ(X, U)] Γ(glued (g * h), U) :=
  LinearMap.mk₂ Γ(X, U) (fun (m : Γ(glued g, U)) (n : Γ(glued h, U)) ↦ mulSec g h m n)
    (mulSec_add_left g h) (mulSec_smul_left g h)
    (mulSec_add_right g h) (mulSec_smul_right g h)

/-- The sectionwise multiplication `glued g ⊗ glued h ⟶ glued (g * h)` of presheaves of
modules. -/
noncomputable def mulPresheafHom : (glued g).val ⊗ (glued h).val ⟶ (glued (g * h)).val where
  app U := ModuleCat.ofHom (TensorProduct.lift (mulBilin g h U.unop))
  naturality := by
    intro U V f
    refine ModuleCat.MonoidalCategory.tensor_ext (fun m n ↦ ?_)
    exact (map_mulSec g h f.unop m n).symm

lemma mulPresheafHom_app_tmul {U : X.Opens} (m : Γ(glued g, U)) (n : Γ(glued h, U)) :
    ((mulPresheafHom g h).app (op U)).hom (m ⊗ₜ n) = mulSec g h m n :=
  rfl

/-- The multiplication morphism `tensorObj (glued g) (glued h) ⟶ glued (g * h)`: the sheaf map
whose sectionwise tensor adjoint is `mulPresheafHom`. -/
noncomputable def mulHom : tensorObj (glued g) (glued h) ⟶ glued (g * h) :=
  (tensorHomEquiv _ _ _).symm (mulPresheafHom g h)

lemma tensorHomEquiv_mulHom : tensorHomEquiv _ _ _ (mulHom g h) = mulPresheafHom g h :=
  (tensorHomEquiv _ _ _).apply_symm_apply _

/-- `mulHom` sends `tmulSec m n` to the componentwise product of `m` and `n`. -/
lemma mulHom_app_tmulSec {U : X.Opens} (m : Γ(glued g, U)) (n : Γ(glued h, U)) :
    (mulHom g h).app U (tmulSec m n) = mulSec g h m n := by
  rw [app_tmulSec, tensorHomEquiv_mulHom]
  rfl

/-- Component formula for `mulHom` on `tmulSec m n`. -/
lemma comp_mulHom_app_tmulSec {U : X.Opens} (m : Γ(glued g, U)) (n : Γ(glued h, U)) (i : ι) :
    comp (g * h) ((mulHom g h).app U (tmulSec m n)) i = comp g m i * comp h n i := by
  rw [mulHom_app_tmulSec]
  rfl

variable {g h} (hg : IsCocycle g) (hh : IsCocycle h)
include hg hh

/-- Over an open inside `T i`, the sectionwise multiplication is bijective: both sides are free
of rank one, on `genSec g i ⊗ genSec h i` and on `genSec (g * h) i`. -/
lemma bijective_mulPresheafHom_app (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    Function.Bijective ((mulPresheafHom g h).app (op V)).hom := by
  let e : ((glued g).val ⊗ (glued h).val).obj (op V) := genSec g hg i hV ⊗ₜ genSec h hh i hV
  let Φ : Γ(X, V) → ((glued g).val ⊗ (glued h).val).obj (op V) := fun c ↦ c • e
  have hΦ : Function.Surjective Φ := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      obtain ⟨α, rfl⟩ := (smul_genSec_bijective g hg i hV).2 a
      obtain ⟨β, rfl⟩ := (smul_genSec_bijective h hh i hV).2 b
      refine ⟨α * β, ?_⟩
      change (α * β) • (genSec g hg i hV ⊗ₜ genSec h hh i hV :
          ((glued g).val ⊗ (glued h).val).obj (op V)) = _
      rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, mul_smul, TensorProduct.smul_tmul']
      exact congrArg (· ⊗ₜ[Γ(X, V)] genSec h hh i hV) (smul_comm α β _)
    | add x y hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, add_smul c d e⟩
  have hcomp : ((mulPresheafHom g h).app (op V)).hom ∘ Φ =
      fun c : Γ(X, V) ↦ c • genSec (g * h) (hg.mul hh) i hV := by
    funext c
    change ((mulPresheafHom g h).app (op V)).hom (c • e) = _
    rw [map_smul, mulPresheafHom_app_tmul, mulSec_genSec]
  have hb : Function.Bijective (((mulPresheafHom g h).app (op V)).hom ∘ Φ) := by
    rw [hcomp]
    exact smul_genSec_bijective (g * h) (hg.mul hh) i hV
  exact (Function.Bijective.of_comp_iff _
    ⟨Function.Injective.of_comp hb.1, hΦ⟩).1 hb

/-- When the `T i` cover `X`, the multiplication morphism is an isomorphism. -/
lemma isIso_mulHom (hT : (⨆ i, T i) = ⊤) : IsIso (mulHom g h) :=
  isIso_of_bijective_tensorHomEquiv (mulHom g h) T hT fun i V hV ↦ by
    rw [tensorHomEquiv_mulHom]
    exact bijective_mulPresheafHom_app hg hh i hV

/-- The tensor product of the line bundles glued from unit cocycles `g` and `h` on a cover is
the line bundle glued from `g * h`. Its forward morphism is `mulHom g h`. -/
noncomputable def tensorIso (hT : (⨆ i, T i) = ⊤) :
    tensorObj (glued g) (glued h) ≅ glued (g * h) :=
  @asIso _ _ _ _ (mulHom g h) (isIso_mulHom hg hh hT)

lemma tensorIso_hom (hT : (⨆ i, T i) = ⊤) : (tensorIso hg hh hT).hom = mulHom g h :=
  rfl

/-- The tensor isomorphism sends `tmulSec m n` to the componentwise product of `m` and `n`. -/
lemma tensorIso_hom_app_tmulSec (hT : (⨆ i, T i) = ⊤) {U : X.Opens} (m : Γ(glued g, U))
    (n : Γ(glued h, U)) :
    (tensorIso hg hh hT).hom.app U (tmulSec m n) = mulSec g h m n :=
  mulHom_app_tmulSec g h m n

/-- The tensor isomorphism sends the tensor of the local generators over `V ≤ T i` to the local
generator of `glued (g * h)`. -/
lemma tensorIso_hom_app_tmulSec_genSec (hT : (⨆ i, T i) = ⊤) (i : ι) {V : X.Opens}
    (hV : V ≤ T i) :
    (tensorIso hg hh hT).hom.app V (tmulSec (genSec g hg i hV) (genSec h hh i hV)) =
      genSec (g * h) (hg.mul hh) i hV := by
  rw [tensorIso_hom_app_tmulSec, mulSec_genSec]

/-- The inverse of the tensor isomorphism sends the local generator of `glued (g * h)` over
`V ≤ T i` to the tensor of the local generators of `glued g` and `glued h`. -/
lemma tensorIso_inv_app_genSec (hT : (⨆ i, T i) = ⊤) (i : ι) {V : X.Opens} (hV : V ≤ T i) :
    (tensorIso hg hh hT).inv.app V (genSec (g * h) (hg.mul hh) i hV) =
      tmulSec (genSec g hg i hV) (genSec h hh i hV) := by
  rw [← tensorIso_hom_app_tmulSec_genSec hg hh hT i hV]
  change ((tensorIso hg hh hT).hom.app V ≫ (tensorIso hg hh hT).inv.app V)
    (tmulSec (genSec g hg i hV) (genSec h hh i hV)) = _
  rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

end Mul

end Langlands.AlgebraicGeometry.Picard.CocycleGluing
