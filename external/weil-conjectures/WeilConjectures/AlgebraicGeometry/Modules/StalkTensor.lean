/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# The stalk of a tensor product of `𝒪_X`-modules

For `𝒪_X`-modules `M` and `N` and a point `x` of `X`, the stalk of `M ⊗ N` at `x` is the tensor
product `M_x ⊗_{𝒪_{X,x}} N_x` of the stalks
(`AlgebraicGeometry.Scheme.Modules.stalkTensorEquiv`).

The tensor product `M ⊗ N` is the sheafification of the presheaf `P : U ↦ M(U) ⊗_{𝒪(U)} N(U)`,
and sheafification does not change the stalks, as the unit `P ⟶ a P` is locally bijective. The
stalk of `P` is the filtered colimit of the `M(U) ⊗_{𝒪(U)} N(U)`, which is `M_x ⊗_{𝒪_{X,x}} N_x`:
the germ maps give a map `P_x → M_x ⊗ N_x`, and the inverse is induced by the balanced map
`(germ m, germ n) ↦ germ (m ⊗ n)`, which is well defined after restricting `m` and `n` to a
common open neighbourhood of `x`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

attribute [local instance] presheafMonoidalCategory

section Restrict

variable (F : TopCat.Presheaf Ab.{u} X)

/-- Restricting twice is restricting along the composite inclusion. -/
lemma presheafAb_map_map_apply {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : F.obj (op U)) :
    F.map (homOfLE h₂).op (F.map (homOfLE h₁).op s) = F.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  rfl

end Restrict

variable (M N : X.Modules) (x : X)

/-- The presheaf tensor product `U ↦ M(U) ⊗_{𝒪(U)} N(U)` of two `𝒪_X`-modules, as a presheaf of
abelian groups. -/
noncomputable abbrev presheafTensor : TopCat.Presheaf Ab.{u} X :=
  (M.val ⊗ N.val).presheaf

variable {M N} in
/-- The section `m ⊗ n` of the presheaf tensor product. -/
noncomputable abbrev ptmul {U : X.Opens} (m : Γ(M, U)) (n : Γ(N, U)) :
    (presheafTensor M N).obj (op U) :=
  (m ⊗ₜ[Γ(X, U)] n : (M.val ⊗ N.val).obj (op U))

variable {M N} in
lemma presheafTensor_map_ptmul {U V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    (presheafTensor M N).map (homOfLE h).op (ptmul m n) =
      ptmul (M.presheaf.map (homOfLE h).op m) (N.presheaf.map (homOfLE h).op n) :=
  rfl

/-- The germ at `x` of a section `m ⊗ n` of the presheaf tensor product, as a biadditive map. -/
noncomputable def germTmul {U : X.Opens} (hx : x ∈ U) : Γ(M, U) →+ Γ(N, U) →+
    (presheafTensor M N).stalk x :=
  AddMonoidHom.mk' (fun m ↦ AddMonoidHom.mk' (fun n ↦ (presheafTensor M N).germ U x hx (ptmul m n))
    fun n n' ↦ by rw [ptmul, TensorProduct.tmul_add]; exact map_add _ _ _)
    fun m m' ↦ by
      ext n
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [ptmul, TensorProduct.add_tmul]
      exact map_add _ _ _

variable {M N x} in
@[simp]
lemma germTmul_apply {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    germTmul M N x hx m n = (presheafTensor M N).germ U x hx (ptmul m n) :=
  rfl

variable {M N x} in
lemma germTmul_map {U V : X.Opens} (h : V ≤ U) (hx : x ∈ V) (m : Γ(M, U)) (n : Γ(N, U)) :
    germTmul M N x hx (M.presheaf.map (homOfLE h).op m) (N.presheaf.map (homOfLE h).op n) =
      germTmul M N x (h hx) m n := by
  rw [germTmul_apply, germTmul_apply, ← presheafTensor_map_ptmul h, TopCat.Presheaf.germ_res_apply]

section PresheafStalk

/-- The map `M(U) ⊗_{𝒪(U)} N(U) → M_x ⊗_{𝒪_{X,x}} N_x`, `m ⊗ n ↦ germ m ⊗ germ n`. -/
noncomputable def tmulGerm {U : X.Opens} (hx : x ∈ U) :
    (presheafTensor M N).obj (op U) →+
      M.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x :=
  TensorProduct.liftAddHom (R := Γ(X, U)) (M := Γ(M, U)) (N := Γ(N, U))
    (AddMonoidHom.mk' (fun m ↦ AddMonoidHom.mk'
      (fun n ↦ M.presheaf.germ U x hx m ⊗ₜ N.presheaf.germ U x hx n)
      fun n n' ↦ by rw [map_add, TensorProduct.tmul_add])
      fun m m' ↦ by
        ext n
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
        rw [map_add, TensorProduct.add_tmul])
    fun r m n ↦ by
      simp only [AddMonoidHom.mk'_apply]
      rw [germ_smul, germ_smul, TensorProduct.smul_tmul]

variable {M N x} in
@[simp]
lemma tmulGerm_ptmul {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    tmulGerm M N x hx (ptmul m n) = M.presheaf.germ U x hx m ⊗ₜ N.presheaf.germ U x hx n :=
  rfl

variable {M N x} in
lemma tmulGerm_map {U V : X.Opens} (h : V ≤ U) (hx : x ∈ V)
    (z : (presheafTensor M N).obj (op U)) :
    tmulGerm M N x hx ((presheafTensor M N).map (homOfLE h).op z) = tmulGerm M N x (h hx) z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
    exact congrArg₂ (· ⊗ₜ ·) (M.presheaf.germ_res_apply (homOfLE h) x hx m)
      (N.presheaf.germ_res_apply (homOfLE h) x hx n)
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

/-- The map from the stalk of the presheaf tensor product to the tensor product of the stalks. -/
noncomputable def presheafTensorStalkToTensor :
    (presheafTensor M N).stalk x →+ M.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x :=
  ConcreteCategory.hom (colimit.desc ((OpenNhds.inclusion x).op ⋙ presheafTensor M N)
    { pt := AddCommGrpCat.of (M.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x)
      ι :=
        { app U := AddCommGrpCat.ofHom (tmulGerm M N x U.unop.2)
          naturality U V i := by
            ext z
            exact tmulGerm_map (leOfHom i.unop) V.unop.2 z } })

variable {M N x} in
@[simp]
lemma presheafTensorStalkToTensor_germ {U : X.Opens} (hx : x ∈ U)
    (z : (presheafTensor M N).obj (op U)) :
    presheafTensorStalkToTensor M N x ((presheafTensor M N).germ U x hx z) =
      tmulGerm M N x hx z := by
  rw [presheafTensorStalkToTensor, TopCat.Presheaf.germ]
  erw [Limits.colimit.ι_desc_apply]
  rfl

variable {M N x} in
/-- The germ of `m|_{U ⊓ V} ⊗ n|_{U ⊓ V}` for sections `m` over `U` and `n` over `V`. -/
noncomputable def germTmulRes {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U)) {V : X.Opens}
    (hxV : x ∈ V) : Γ(N, V) →+ (presheafTensor M N).stalk x :=
  (germTmul M N x (U := U ⊓ V) ⟨hx, hxV⟩ (M.presheaf.map (homOfLE inf_le_left).op m)).comp
    (N.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom

variable {M N x} in
lemma germTmulRes_apply {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U)) {V : X.Opens}
    (hxV : x ∈ V) (n : Γ(N, V)) :
    germTmulRes hx m hxV n = germTmul M N x (U := U ⊓ V) ⟨hx, hxV⟩
      (M.presheaf.map (homOfLE inf_le_left).op m) (N.presheaf.map (homOfLE inf_le_right).op n) :=
  rfl

variable {M N x} in
lemma germTmulRes_map {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U)) {V V' : X.Opens} (h : V' ≤ V)
    (hxV' : x ∈ V') (n : Γ(N, V)) :
    germTmulRes hx m hxV' (N.presheaf.map (homOfLE h).op n) = germTmulRes hx m (h hxV') n := by
  rw [germTmulRes_apply, germTmulRes_apply,
    ← germTmul_map (inf_le_inf_left U h) ⟨hx, hxV'⟩, presheafAb_map_map_apply M.presheaf,
    presheafAb_map_map_apply N.presheaf, presheafAb_map_map_apply N.presheaf]

variable {M N x} in
/-- For a section `m` of `M` over a neighbourhood `U` of `x`, the map `N_x → P_x`,
`germ n ↦ germ (m ⊗ n)`, with values in the stalk of the presheaf tensor product. -/
noncomputable def germTmulStalk {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U)) :
    N.presheaf.stalk x →+ (presheafTensor M N).stalk x :=
  ConcreteCategory.hom (colimit.desc ((OpenNhds.inclusion x).op ⋙ N.presheaf)
    { pt := (presheafTensor M N).stalk x
      ι :=
        { app V := AddCommGrpCat.ofHom (germTmulRes hx m V.unop.2)
          naturality V V' i := by
            ext n
            exact germTmulRes_map hx m (leOfHom i.unop) V'.unop.2 n } })

variable {M N x} in
@[simp]
lemma germTmulStalk_germ {U V : X.Opens} (hx : x ∈ U) (hx' : x ∈ V) (m : Γ(M, U))
    (n : Γ(N, V)) :
    germTmulStalk hx m (N.presheaf.germ V x hx' n) =
      germTmul M N x (U := U ⊓ V) ⟨hx, hx'⟩ (M.presheaf.map (homOfLE inf_le_left).op m)
        (N.presheaf.map (homOfLE inf_le_right).op n) := by
  rw [germTmulStalk, TopCat.Presheaf.germ]
  erw [Limits.colimit.ι_desc_apply]
  rfl

variable {M N x} in
lemma germTmulStalk_map {U U' : X.Opens} (h : U' ≤ U) (hx : x ∈ U') (m : Γ(M, U)) :
    germTmulStalk hx (M.presheaf.map (homOfLE h).op m) = germTmulStalk (N := N) (h hx) m := by
  refine AddMonoidHom.ext fun b ↦ ?_
  obtain ⟨V, hxV, n, rfl⟩ := N.presheaf.exists_germ_eq b
  have h' : U' ⊓ V ≤ U ⊓ V := inf_le_inf_right _ h
  rw [germTmulStalk_germ, germTmulStalk_germ, ← germTmul_map h' ⟨hx, hxV⟩,
    presheafAb_map_map_apply, presheafAb_map_map_apply, presheafAb_map_map_apply]

/-- The biadditive map `M_x × N_x → P_x`, `(germ m, germ n) ↦ germ (m ⊗ n)`. -/
noncomputable def germTmulStalk₂ :
    M.presheaf.stalk x →+ N.presheaf.stalk x →+ (presheafTensor M N).stalk x :=
  ConcreteCategory.hom (colimit.desc ((OpenNhds.inclusion x).op ⋙ M.presheaf)
    { pt := AddCommGrpCat.of (N.presheaf.stalk x →+ (presheafTensor M N).stalk x)
      ι :=
        { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun m ↦ germTmulStalk U.unop.2 m)
            fun m m' ↦ by
              refine AddMonoidHom.ext fun b ↦ ?_
              obtain ⟨V, hxV, n, rfl⟩ := N.presheaf.exists_germ_eq b
              rw [AddMonoidHom.add_apply, germTmulStalk_germ, germTmulStalk_germ,
                germTmulStalk_germ, map_add, map_add, AddMonoidHom.add_apply])
          naturality U U' i := by
            refine AddCommGrpCat.ext fun m ↦ ?_
            exact germTmulStalk_map (leOfHom i.unop) U'.unop.2 m } })

variable {M N x} in
lemma germTmulStalk₂_germ {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U)) :
    germTmulStalk₂ M N x (M.presheaf.germ U x hx m) = germTmulStalk hx m := by
  rw [germTmulStalk₂, TopCat.Presheaf.germ]
  erw [Limits.colimit.ι_desc_apply]
  rfl

variable {M N x} in
lemma germTmulStalk₂_germ_germ {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    germTmulStalk₂ M N x (M.presheaf.germ U x hx m) (N.presheaf.germ U x hx n) =
      germTmul M N x hx m n := by
  rw [germTmulStalk₂_germ, germTmulStalk_germ, germTmul_map]

/-- The map from the tensor product of the stalks to the stalk of the presheaf tensor product. -/
noncomputable def tensorToPresheafTensorStalk :
    M.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x →+ (presheafTensor M N).stalk x :=
  TensorProduct.liftAddHom (germTmulStalk₂ M N x) fun r a b ↦ by
    obtain ⟨W, hxW, ρ, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq a
    obtain ⟨V, hxV, n, rfl⟩ := N.presheaf.exists_germ_eq b
    have hx : x ∈ W ⊓ U ⊓ V := ⟨⟨hxW, hxU⟩, hxV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left.trans inf_le_left) :
        W ⊓ U ⊓ V ⟶ W) x hx,
      ← M.presheaf.germ_res_apply (homOfLE (inf_le_left.trans inf_le_right) :
        W ⊓ U ⊓ V ⟶ U) x hx,
      ← N.presheaf.germ_res_apply (homOfLE inf_le_right : W ⊓ U ⊓ V ⟶ V) x hx,
      ← germ_smul, ← germ_smul, germTmulStalk₂_germ_germ, germTmulStalk₂_germ_germ,
      germTmul_apply, germTmul_apply, ptmul, ptmul, TensorProduct.smul_tmul]

variable {M N x} in
@[simp]
lemma tensorToPresheafTensorStalk_germ_tmul_germ {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U))
    (n : Γ(N, U)) :
    tensorToPresheafTensorStalk M N x (M.presheaf.germ U x hx m ⊗ₜ N.presheaf.germ U x hx n) =
      (presheafTensor M N).germ U x hx (ptmul m n) :=
  germTmulStalk₂_germ_germ hx m n

/-- **The stalk of the presheaf tensor product is the tensor product of the stalks.** -/
noncomputable def presheafTensorStalkEquiv :
    (presheafTensor M N).stalk x ≃+ M.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x :=
  AddEquiv.ofBijective (presheafTensorStalkToTensor M N x) <| by
    refine Function.bijective_iff_has_inverse.2 ⟨tensorToPresheafTensorStalk M N x,
      fun z ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨U, hxU, z, rfl⟩ := (presheafTensor M N).exists_germ_eq z
      rw [presheafTensorStalkToTensor_germ]
      induction z using TensorProduct.inductionOn with
      | tmul m n => exact tensorToPresheafTensorStalk_germ_tmul_germ hxU m n
      | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]
    · induction z using TensorProduct.inductionOn with
      | tmul a b =>
        obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq a
        obtain ⟨V, hxV, n, rfl⟩ := N.presheaf.exists_germ_eq b
        have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
        rw [← M.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx,
          ← N.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx,
          tensorToPresheafTensorStalk_germ_tmul_germ, presheafTensorStalkToTensor_germ,
          tmulGerm_ptmul]
      | add z z' hz hz' => rw [map_add, map_add, hz, hz']

variable {M N x} in
@[simp]
lemma presheafTensorStalkEquiv_germ_ptmul {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U))
    (n : Γ(N, U)) :
    presheafTensorStalkEquiv M N x ((presheafTensor M N).germ U x hx (ptmul m n)) =
      M.presheaf.germ U x hx m ⊗ₜ N.presheaf.germ U x hx n :=
  presheafTensorStalkToTensor_germ hx _

end PresheafStalk

/-- A locally injective morphism of presheaves of abelian groups on a topological space is
injective on stalks. -/
lemma _root_.TopCat.Presheaf.injective_stalkFunctor_map_of_isLocallyInjective
    {Y : TopCat.{u}} {F G : TopCat.Presheaf Ab.{u} Y} (T : F ⟶ G)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) T] (y : Y) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map T) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ?_
  obtain ⟨U, hyU, a, rfl⟩ := F.exists_germ_eq s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← map_zero (ConcreteCategory.hom (G.germ U y hyU))] at hs
  obtain ⟨W, hyW, iU, iU', hW⟩ := G.germ_eq y hyU hyU _ _ hs
  rw [map_zero] at hW
  have hT : T.app (op W) (F.map iU.op a) = T.app (op W) 0 := by
    rw [← ConcreteCategory.comp_apply, T.naturality, ConcreteCategory.comp_apply, hW, map_zero]
  obtain ⟨V, iV, hV, hyV⟩ := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology Y) T _ _ hT
    y hyW
  rw [← F.germ_res_apply iU y hyW, ← F.germ_res_apply iV y hyV]
  simp only [Presheaf.equalizerSieve_apply] at hV
  rw [hV, map_zero, map_zero]

attribute [local instance] forgetToPresheafOfModulesLaxMonoidal

/-- The map from the presheaf tensor product to the underlying presheaf of `M ⊗ N`, sending
`m ⊗ n` to `tmulSection m n`. It is locally bijective. -/
noncomputable abbrev presheafTensorToTensor : presheafTensor M N ⟶ (M ⊗ N).presheaf :=
  (_root_.PresheafOfModules.toPresheaf _).map
    (Functor.LaxMonoidal.μ (forgetToPresheafOfModules X) M N)

variable {M N} in
lemma presheafTensorToTensor_app_ptmul {U : X.Opens} (m : Γ(M, U)) (n : Γ(N, U)) :
    (presheafTensorToTensor M N).app (op U) (ptmul m n) = tmulSection m n :=
  rfl

lemma bijective_stalkFunctor_map_presheafTensorToTensor :
    Function.Bijective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map (presheafTensorToTensor M N)) :=
  ⟨TopCat.Presheaf.injective_stalkFunctor_map_of_isLocallyInjective _ x,
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).1
      (inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (presheafTensorToTensor M N))) x⟩

/-- **The stalk of a tensor product is the tensor product of the stalks.** For `𝒪_X`-modules
`M` and `N` and a point `x`, `(M ⊗ N)_x ≅ M_x ⊗_{𝒪_{X,x}} N_x`, with `germ (m ⊗ n)` corresponding
to `germ m ⊗ germ n`. -/
noncomputable def stalkTensorEquiv :
    (M ⊗ N).presheaf.stalk x ≃+ M.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x :=
  (AddEquiv.ofBijective _ (bijective_stalkFunctor_map_presheafTensorToTensor M N x)).symm.trans
    (presheafTensorStalkEquiv M N x)

variable {M N x} in
lemma germ_tmulSection_eq {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    (M ⊗ N).presheaf.germ U x hx (tmulSection m n) =
      (TopCat.Presheaf.stalkFunctor Ab.{u} x).map (presheafTensorToTensor M N)
        ((presheafTensor M N).germ U x hx (ptmul m n)) := by
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, presheafTensorToTensor_app_ptmul]

variable {M N x} in
@[simp]
lemma stalkTensorEquiv_germ_tmulSection {U : X.Opens} (hx : x ∈ U) (m : Γ(M, U))
    (n : Γ(N, U)) :
    stalkTensorEquiv M N x ((M ⊗ N).presheaf.germ U x hx (tmulSection m n)) =
      M.presheaf.germ U x hx m ⊗ₜ N.presheaf.germ U x hx n := by
  rw [stalkTensorEquiv, AddEquiv.trans_apply, germ_tmulSection_eq]
  erw [(AddEquiv.ofBijective _
    (bijective_stalkFunctor_map_presheafTensorToTensor M N x)).symm_apply_apply]
  exact presheafTensorStalkEquiv_germ_ptmul hx m n

variable {M N x} in
/-- Every element of the stalk of `M ⊗ N` is a sum of germs of sections `m ⊗ n`. -/
lemma stalk_tensor_induction {p : (M ⊗ N).presheaf.stalk x → Prop}
    (z : (M ⊗ N).presheaf.stalk x) (zero : p 0) (add : ∀ a b, p a → p b → p (a + b))
    (tmul : ∀ (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) (n : Γ(N, U)),
      p ((M ⊗ N).presheaf.germ U x hx (tmulSection m n))) : p z := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact zero
  clear hz
  obtain ⟨w, rfl⟩ := (bijective_stalkFunctor_map_presheafTensorToTensor M N x).2 z
  obtain ⟨U, hx, y, rfl⟩ := (presheafTensor M N).exists_germ_eq w
  induction y using TensorProduct.inductionOn with
  | tmul m n => exact (germ_tmulSection_eq hx m n) ▸ tmul U hx m n
  | add y y' hy hy' => rw [map_add, map_add]; exact add _ _ hy hy'

variable {M N} in
/-- Naturality of `AlgebraicGeometry.Scheme.Modules.stalkTensorEquiv` in the first variable. -/
lemma stalkTensorEquiv_naturality {M' : X.Modules} (φ : M ⟶ M')
    (z : (M ⊗ N).presheaf.stalk x) :
    stalkTensorEquiv M' N x ((φ ▷ N).stalkLinearMap x z) =
      LinearMap.rTensor _ (φ.stalkLinearMap x) (stalkTensorEquiv M N x z) := by
  refine stalk_tensor_induction (p := fun z ↦
      stalkTensorEquiv M' N x ((φ ▷ N).stalkLinearMap x z) =
        LinearMap.rTensor _ (φ.stalkLinearMap x) (stalkTensorEquiv M N x z)) z ?_
    (fun a b ha hb ↦ ?_) (fun U hx m n ↦ ?_)
  · simp only [map_zero]
  · rw [map_add, map_add, map_add, map_add, ha, hb]
  · rw [Hom.stalkLinearMap_germ, whiskerRight_app_tmulSection, stalkTensorEquiv_germ_tmulSection,
      stalkTensorEquiv_germ_tmulSection, LinearMap.rTensor_tmul, Hom.stalkLinearMap_germ]


section Skyscraper

variable (I : Type u) [AddCommGroup I] [Module (X.presheaf.stalk x) I]

/-- The stalk at `x` of the skyscraper module at `x` with value `I` is `I`. -/
noncomputable def skyscraperStalkLinearEquiv :
    (skyscraper x I).presheaf.stalk x ≃ₗ[X.presheaf.stalk x] I :=
  LinearEquiv.ofBijective (skyscraperStalkEval x I) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_, fun i ↦ ?_⟩
    · obtain ⟨U, hxU, s, rfl⟩ := (skyscraper x I).presheaf.exists_germ_eq s
      rw [skyscraperStalkEval_germ] at hs
      have : s = 0 := SkyscraperSections.ext fun hx ↦ hs
      rw [this, map_zero]
    · exact ⟨(skyscraper x I).presheaf.germ ⊤ x (by trivial) (fun _ ↦ i),
        skyscraperStalkEval_germ x I (by trivial) _⟩

end Skyscraper

end AlgebraicGeometry.Scheme.Modules
