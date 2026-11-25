/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeSections
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Global sections of an invertible module after a field extension

Let `X` be a quasi-compact scheme over a field `k`, let `K / k` be a field extension, with
projections `φ : X_K ⟶ X` and `p : X_K ⟶ Spec K`, and let `M` be an invertible `𝒪_X`-module.
Every global section of `φ^* M` is a finite `K`-linear combination of pullbacks of global
sections of `M`: this is the surjectivity of `Γ(X, M) ⊗_k K ⟶ Γ(X_K, φ^* M)` in flat base change.

On an affine open `W` on which `M` has a free generator `e`, a section of `φ^* M` is
`h • φ^* e` with `h ∈ Γ(X_K, φ⁻¹ W) = Γ(X, W) ⊗_k K`
(`AlgebraicGeometry.exists_ringEquiv_tensor_app_preimage_fst`). Expanding these finitely many
tensors along one `k`-linearly independent family `β` of `K`, the coefficients of the `β q`
are local sections of `M` which glue, since `Γ(X, V) ⊗_k K ⟶ Γ(X_K, φ⁻¹ V)` is injective on
affine opens `V`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.pullbackTopSection`: the pullback of a global section.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackTopSection`: the sections of
  `φ^* M` are spanned over `K` by pullbacks of sections of `M`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

section PullbackTop

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules}

/-- The pullback `g^* m` of a global section `m` of `M`, as a global section of `g^* M`. -/
noncomputable def pullbackTopSection (m : Γ(M, ⊤)) : Γ((pullback g).obj M, ⊤) :=
  ((pullback g).obj M).presheaf.map (homOfLE (g.preimage_top).ge).op
    (pullbackSection g m)

lemma pullbackTopSection_map (m : Γ(M, ⊤)) {V : Y.Opens} :
    ((pullback g).obj M).presheaf.map (homOfLE (le_top : g ⁻¹ᵁ V ≤ ⊤)).op
        (pullbackTopSection g m) =
      pullbackSection g (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m) := by
  rw [pullbackTopSection, presheaf_map_homOfLE_map_homOfLE, pullbackSection_map]

lemma pullbackSection_sub {U : Y.Opens} (m m' : Γ(M, U)) :
    pullbackSection g (m - m') = pullbackSection g m - pullbackSection g m' :=
  map_sub _ _ _

/-- The pullback of a global section generates the pullback module wherever the section
generates the module. -/
lemma preimage_generatingLocus_le (m : Γ(M, ⊤)) :
    g ⁻¹ᵁ generatingLocus m ≤ generatingLocus (pullbackTopSection g m) := fun _ hx ↦
  ⟨g ⁻¹ᵁ generatingLocus m, hx, by
    rw [pullbackTopSection_map]
    exact (isFreeGenerator_generatingLocus m).pullback_unit_app g⟩

/-- **Linear combinations of pullbacks of sections.** If a linear combination
`∑ r, a r • g^* (σ r)` of pullbacks of global sections of an invertible module `M` generates
`g^* M` at `y`, then some `σ r` generates `M` at `g y`. -/
lemma exists_generatesAt_of_generatesAt_sum [SheafOfModules.IsInvertible.{u, u, u} M]
    {ι : Type*} (s : Finset ι) (a : ι → Γ(X, ⊤)) (σ : ι → Γ(M, ⊤)) {y : X}
    (h : GeneratesAt (∑ r ∈ s, a r • pullbackTopSection g (σ r)) y) :
    ∃ r ∈ s, GeneratesAt (σ r) (g y) := by
  classical
  by_contra hne
  simp only [not_exists, not_and] at hne
  obtain ⟨W, hxW, -, e, he⟩ := exists_isFreeGenerator M (x := g y) (W := ⊤) trivial
  set f : ι → Γ(Y, W.1) := fun r ↦ he.coeff (M.presheaf.map (homOfLE le_top).op (σ r))
  have hf (r : ι) : M.presheaf.map (homOfLE le_top).op (σ r) = f r • e := (he.coeff_smul _).symm
  have hgen : IsFreeGenerator (pullbackSection g e) := he.pullback_unit_app g
  have hsum : ((pullback g).obj M).presheaf.map (homOfLE (le_top : g ⁻¹ᵁ W.1 ≤ ⊤)).op
      (∑ r ∈ s, a r • pullbackTopSection g (σ r)) =
      (∑ r ∈ s, X.presheaf.map (homOfLE le_top).op (a r) * g.app W.1 (f r)) •
        pullbackSection g e := by
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [Scheme.Modules.map_smul, pullbackTopSection_map, hf, pullbackSection_smul, smul_smul]
  have hy := mem_basicOpen_of_generatesAt hgen hsum hxW h
  have hle (t : Finset ι) : X.basicOpen (∑ r ∈ t, X.presheaf.map (homOfLE le_top).op (a r) *
      g.app W.1 (f r)) ≤ ⨆ r ∈ t, X.basicOpen (g.app W.1 (f r)) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert r s hr ih =>
      rw [Finset.sum_insert hr]
      refine (X.basicOpen_add_le _ _).trans (sup_le ?_ (ih.trans ?_))
      · rw [X.basicOpen_mul]
        exact inf_le_right.trans (le_iSup₂_of_le r (Finset.mem_insert_self r s) le_rfl)
      · exact iSup₂_le fun r' hr' ↦ le_iSup₂_of_le r' (Finset.mem_insert_of_mem hr') le_rfl
  obtain ⟨r, hr, hyr⟩ : ∃ r ∈ s, y ∈ X.basicOpen (g.app W.1 (f r)) := by
    simpa only [TopologicalSpace.Opens.mem_iSup, exists_prop] using hle s hy
  rw [← Scheme.preimage_basicOpen] at hyr
  exact hne r hr (generatesAt_of_mem_basicOpen he (hf r) hyr)

end PullbackTop

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

private lemma appLE_res {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U) (h : V' ≤ V) (x : Γ(Y, U)) :
    X.presheaf.map (homOfLE h).op (f.appLE U V e x) = f.appLE U V' e' x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private lemma res_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f ⁻¹ᵁ U') (h : U ≤ U') (x : Γ(Y, U')) :
    f.appLE U V e (Y.presheaf.map (homOfLE h).op x) = f.appLE U' V e' x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- **Injectivity of `Γ(X, W) ⊗_k K ⟶ Γ(X_K, φ⁻¹ W)` on an affine open**, in the form: if
`∑ φ^♯ (a q) · β q = 0` for a `k`-linearly independent family `β` of `K`, then all `a q`
vanish. -/
lemma eq_zero_of_sum_appLE_mul_eq_zero_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W)
    {N : ℕ} {β : Fin N → K} (hβ : LinearIndependent k β) (a : Fin N → Γ(X, W))
    (h : ∑ q, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appLE W _ le_rfl
        (a q) * (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appLE ⊤ _
          le_top ((Scheme.ΓSpecIso (.of K)).inv (β q)) = 0) (q : Fin N) : a q = 0 := by
  let : Algebra k Γ(X, W) :=
    ((f.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  obtain ⟨e, he₁, he₂⟩ := exists_ringEquiv_tensor_app_preimage_fst (R := K) f hW
  have key (x : Γ(X, W)) (r : K) : e (x ⊗ₜ r) =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appLE W _ le_rfl x *
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appLE ⊤ _ le_top
          ((Scheme.ΓSpecIso (.of K)).inv r) := by
    have : x ⊗ₜ[k] r = (x ⊗ₜ[k] (1 : K)) * ((1 : Γ(X, W)) ⊗ₜ[k] r) := by simp
    rw [this, map_mul, he₁, he₂, Scheme.Hom.app_eq_appLE]
  have h' : ∑ q, a q • ((1 : Γ(X, W)) ⊗ₜ[k] β q) = 0 := by
    apply e.injective
    rw [map_zero, map_sum]
    simp_rw [smul_tmul', smul_eq_mul, mul_one, key]
    exact h
  have hli : LinearIndependent Γ(X, W) fun q ↦ (1 : Γ(X, W)) ⊗ₜ[k] β q :=
    Module.Flat.linearIndependent_one_tmul hβ
  exact Fintype.linearIndependent_iff.mp hli a h' q

/-- **Injectivity of `Γ(X, V) ⊗_k K ⟶ Γ(X_K, φ⁻¹ V)`** on an arbitrary open `V`, in the form:
if `∑ φ^♯ (a q) · β q = 0` for a `k`-linearly independent family `β` of `K`, then all `a q`
vanish. This reduces to affine opens, which form a basis. -/
lemma eq_zero_of_sum_appLE_mul_eq_zero {V : X.Opens}
    {N : ℕ} {β : Fin N → K} (hβ : LinearIndependent k β) (a : Fin N → Γ(X, V))
    (h : ∑ q, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appLE V _ le_rfl
        (a q) * (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appLE ⊤ _
          le_top ((Scheme.ΓSpecIso (.of K)).inv (β q)) = 0) (q : Fin N) : a q = 0 := by
  set φ := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  set p := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let ι := {Z : X.affineOpens // Z.1 ≤ V}
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun Z : ι ↦ Z.1.1) V
    (fun Z ↦ homOfLE Z.2) (fun x hx ↦ ?_) _ _ fun Z ↦ ?_
  · obtain ⟨Z, hZ, hxZ, hZV⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := V) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨Z, hZ⟩, hZV⟩, hxZ⟩
  · change X.presheaf.map (homOfLE Z.2).op (a q) = X.presheaf.map (homOfLE Z.2).op 0
    rw [map_zero]
    refine eq_zero_of_sum_appLE_mul_eq_zero_of_isAffineOpen f Z.1.2 hβ
      (fun q ↦ X.presheaf.map (homOfLE Z.2).op (a q)) ?_ q
    have h' := congrArg ((Limits.pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap k K)))).presheaf.map (homOfLE (φ.preimage_mono Z.2)).op) h
    simp only [map_sum, map_mul, map_zero] at h'
    convert h' using 3 with q
    · exact (res_appLE _ _ (φ.preimage_mono Z.2) _ _).trans (appLE_res _ _ _ _ _).symm
    · exact (appLE_res _ _ _ _ _).symm

/-- **Sections of an invertible module after a field extension.** Let `X` be a quasi-compact
scheme over a field `k`, let `K / k` be a field extension, with projections `φ : X_K ⟶ X` and
`p : X_K ⟶ Spec K`, and let `M` be an invertible `𝒪_X`-module. Then every global section of
`φ^* M` is a finite sum `∑ q, p^♯ (c q) • φ^* (t q)` with `c q ∈ K` and `t q ∈ Γ(X, M)`. -/
theorem exists_eq_sum_smul_pullbackTopSection [CompactSpace X] (M : X.Modules) [M.IsInvertible]
    (σ : Γ((pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M,
      ⊤)) :
    ∃ (N : ℕ) (c : Fin N → K) (t : Fin N → Γ(M, ⊤)),
      σ = ∑ q, (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
        ((Scheme.ΓSpecIso (.of K)).inv (c q)) •
          pullbackTopSection (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (t q) := by
  classical
  revert σ
  set φ := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  set p := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  set MK := (pullback φ).obj M
  intro σ
  let pK (V : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens)
      (c : K) : Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))), V) :=
    p.appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of K)).inv c)
  have := IsInvertible.sheafOfModules_isInvertible M
  -- a finite cover by affine opens with free generators
  choose W hxW _ e he using fun x : X ↦ exists_isFreeGenerator M (x := x) (W := ⊤) trivial
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((W x).1 : Set X))
    (fun x ↦ (W x).1.2) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxW x⟩)
  have hcov (x : X) : ∃ a : S, x ∈ (W a).1 := by
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩
  -- the coefficient `h a` of `σ` with respect to the pulled back generator `φ^* e a`
  have hpe (a : S) : IsFreeGenerator (pullbackSection φ (e a)) := (he a).pullback_unit_app φ
  let h (a : S) : Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      φ ⁻¹ᵁ (W a).1) :=
    (hpe a).coeff (MK.presheaf.map (homOfLE le_top).op σ)
  have hh (a : S) : h a • pullbackSection φ (e a) = MK.presheaf.map (homOfLE le_top).op σ :=
    (hpe a).coeff_smul _
  -- expand the `h a` along a linearly independent family `β` of `K`
  let inst (a : S) : Algebra k Γ(X, (W a).1) :=
    ((f.appLE ⊤ (W a).1 le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  choose E hE₁ hE₂ using fun a : S ↦ exists_ringEquiv_tensor_app_preimage_fst (R := K) f (W a).2
  obtain ⟨N, β, hβ, hF⟩ := TensorProduct.exists_linearIndependent_forall_eq_sum_tmul
    (A := fun a : S ↦ Γ(X, (W a).1)) (fun a ↦ (E a).symm (h a))
  choose F hF using hF
  have hhF (a : S) : h a = ∑ q, φ.appLE (W a).1 _ le_rfl (F a q) * pK (φ ⁻¹ᵁ (W a).1) (β q) := by
    rw [← (E a).apply_symm_apply (h a), hF a, map_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have : F a q ⊗ₜ[k] β q = (F a q ⊗ₜ[k] (1 : K)) * ((1 : Γ(X, (W a).1)) ⊗ₜ[k] β q) := by
      simp
    rw [this, map_mul, hE₁, hE₂, Scheme.Hom.app_eq_appLE]
  -- on `φ⁻¹ V` for `V ⊆ W a`, `σ = ∑ q, β q • φ^* (F a q • e a)`
  have hσ (a : S) {V : X.Opens} (hV : V ≤ (W a).1) :
      MK.presheaf.map (homOfLE le_top : φ ⁻¹ᵁ V ⟶ ⊤).op σ =
        ∑ q, pK (φ ⁻¹ᵁ V) (β q) •
          pullbackSection φ (M.presheaf.map (homOfLE hV).op (F a q • e a)) := by
    have h1 := congrArg (MK.presheaf.map (homOfLE (φ.preimage_mono hV)).op) (hh a)
    rw [presheaf_map_homOfLE_map_homOfLE, map_smul, hhF a] at h1
    rw [← h1, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [map_smul, pullbackSection_smul, pullbackSection_map, map_mul, smul_smul, mul_comm,
      appLE_res _ _ (φ.preimage_mono hV), Scheme.Hom.app_eq_appLE,
      res_appLE _ _ (φ.preimage_mono hV)]
    congr 2
    exact appLE_res _ _ _ _ _
  -- the local sections `F a q • e a` agree on overlaps
  have hcompat (q : Fin N) : TopCat.Presheaf.IsCompatible M.presheaf (fun a : S ↦ (W a).1)
      (fun a ↦ F a q • e a) := by
    intro a b
    set U := (W a).1 ⊓ (W b).1
    have heb := (he b).map (inf_le_right : U ≤ (W b).1)
    let D (q' : Fin N) : Γ(M, U) := M.presheaf.map (homOfLE inf_le_left).op (F a q' • e a) -
      M.presheaf.map (homOfLE inf_le_right).op (F b q' • e b)
    let δ (q' : Fin N) : Γ(X, U) := heb.coeff (D q')
    have hδ : ∀ q', δ q' = 0 := by
      refine eq_zero_of_sum_appLE_mul_eq_zero f hβ δ ?_
      have hpeb : IsFreeGenerator (pullbackSection φ (M.presheaf.map
          (homOfLE (inf_le_right : U ≤ (W b).1)).op (e b))) := heb.pullback_unit_app φ
      refine hpeb.smul_left_injective ?_
      dsimp only
      rw [zero_smul, Finset.sum_smul]
      have h3 : ∑ q', pK (φ ⁻¹ᵁ U) (β q') • pullbackSection φ (D q') = 0 := by
        simp only [D, pullbackSection_sub, smul_sub, Finset.sum_sub_distrib]
        rw [← hσ a (inf_le_left : U ≤ (W a).1), ← hσ b (inf_le_right : U ≤ (W b).1), sub_self]
      rw [← h3]
      refine Finset.sum_congr rfl fun q' _ ↦ ?_
      rw [← heb.coeff_smul (D q'), pullbackSection_smul, smul_smul, mul_comm,
        Scheme.Hom.app_eq_appLE]
    have hD : D q = 0 := by rw [← heb.coeff_smul (D q)]; simp [δ, hδ q]
    exact sub_eq_zero.mp hD
  -- glue them to global sections `t q`
  choose t ht using fun q ↦ (TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩
    (fun a : S ↦ (W a).1) ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr (hcov x)) (fun a ↦ F a q • e a)
    (hcompat q)).exists
  refine ⟨N, β, t, TopCat.Sheaf.eq_of_locally_eq' ⟨MK.presheaf, MK.isSheaf⟩
    (fun a : S ↦ φ ⁻¹ᵁ (W a).1) ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr (hcov (φ x))) _ _ fun a ↦ ?_⟩
  change MK.presheaf.map (homOfLE le_top).op σ = MK.presheaf.map (homOfLE le_top).op _
  rw [hσ a le_rfl, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [presheaf_map_id_apply, ← ht q a, ← pullbackTopSection_map, map_smul]
  congr 1

end AlgebraicGeometry.Scheme.Modules
