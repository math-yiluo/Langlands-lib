/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.Reductions
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.PointCount

/-!
# Étale cohomology of curves in degrees at least three

Let `C` be a curve over an algebraically closed field `k`. Assuming that `H²` of torsion sheaves
vanishes on affine curves over `k`, we show that `Hᵠ(C, F) = 0` for every torsion sheaf `F` and
`q ≥ 3`.

Choose an affine open `j : U ⟶ C` whose complement is a finite set of closed points
(`AlgebraicGeometry.IsCurve.exists_isAffineOpen_finite_compl`). The unit `F ⟶ j_* j^* F` is an
isomorphism over `U`, so it induces isomorphisms on `Hᵠ` for `q ≥ 2`. For a sheaf `G` on `U`
killed by `n`, embed `G` into an acyclic sheaf `J` killed by `n` whose pushforward is acyclic
(`AlgebraicGeometry.Etale.exists_mono_acyclic_of_nsmul_eq_zero`), with cokernel `G'`. The
sequence `0 → j_* G → j_* J → j_* G'` is exact, and the cokernel of its last map vanishes over
`U`, hence is acyclic; this gives `H³(C, j_* G) ↪ H²(C, j_* G')`. Embedding `G'` in the same way,
with cokernel `G''`, the map `j_* J' → j_* G''` is now an epimorphism: over an affine étale
`C`-scheme `V`, the scheme `V ×_C U` is an affine curve, so `H¹(V ×_C U, G') ≅ H²(V ×_C U, G)`
vanishes. Hence `H²(C, j_* G') ↪ H¹(C, j_* G'') ↪ H¹(U, G'') ≅ H²(U, G') = 0`. Degrees `q > 3`
follow by dimension shifting on `C`.

## Main statements

- `AlgebraicGeometry.IsCurve.exists_isAffineOpen_finite_compl`: a curve has an affine open whose
  complement is a finite set of closed points.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_of_forall`: vanishing in degrees at
  least three, assuming the vanishing of `H²` on affine curves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry

/-- The residue field of a closed point of a scheme locally of finite type over an algebraically
closed field `k` is algebraically closed: it is a finite extension of `k`. -/
lemma Scheme.isAlgClosed_residueField_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) : IsAlgClosed (X.residueField x) := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x ≫ f)).mpr inferInstance
  rw [← f.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff] at this
  have : Module.Finite k (X.residueField x) := this
  exact IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective (algebraMap k _)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)))

open scoped Etale

variable {k : Type u} [Field k] {C : Scheme.{u}}

section Colimits

variable {X : Scheme.{u}}

/-- A section of a sheaf which is killed by a morphism lifts to the kernel. -/
lemma Etale.exists_kernel_ι_app_eq {G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ψ : G ⟶ H) {W : X.Etale} (x : G.obj.obj (op W)) (hx : ψ.hom.app (op W) x = 0) :
    ∃ t : (kernel ψ).obj.obj (op W), (kernel.ι ψ).hom.app (op W) t = x := by
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op W)
  let e := PreservesKernel.iso E ψ ≪≫ AddCommGrpCat.kernelIsoKer (E.map ψ)
  refine ⟨e.inv ⟨x, hx⟩, ?_⟩
  have h₁ := PreservesKernel.iso_inv_ι E ψ
  have h₂ := AddCommGrpCat.kernelIsoKer_inv_comp_ι (E.map ψ)
  change (e.inv ≫ E.map (kernel.ι ψ)) ⟨x, hx⟩ = x
  rw [Iso.trans_inv, Category.assoc, h₁, h₂]
  rfl

/-- **Filtered unions of subsheaves.** Let `c` be a cocone over a filtered diagram of abelian
étale sheaves whose legs are monomorphisms. If every section of the cocone point lies, locally,
in the image of some leg, then `c` is a colimit cocone: the comparison map from the colimit is a
monomorphism since filtered colimits are exact, and an epimorphism since it is locally
surjective. -/
noncomputable def Etale.isColimitOfMonoOfLocallySurjective {J : Type u} [SmallCategory J]
    [IsFiltered J] {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (c : Cocone D)
    [∀ j, Mono (c.ι.app j)]
    (h : ∀ (V : X.Etale) (s : c.pt.obj.obj (op V)), ∃ R ∈ X.smallEtaleTopology V,
      ∀ ⦃W : X.Etale⦄ (g : W ⟶ V), R g →
        ∃ (j : J) (t : (D.obj j).obj.obj (op W)),
          (c.ι.app j).hom.app (op W) t = c.pt.obj.map g.op s) :
    IsColimit c := by
  have : AB5OfSize.{u, u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have : IsConnected J := IsFiltered.isConnected _
  let φ := colimit.desc D c
  have hmono : Mono φ := by
    let α : D ⟶ (Functor.const _).obj c.pt := { app j := c.ι.app j }
    have : Mono α := NatTrans.mono_of_mono_app _
    have : Mono (colim.map α) := inferInstance
    let e := (colimit.isColimit ((Functor.const J).obj c.pt)).coconePointUniqueUpToIso
      (isColimitConstCocone J c.pt)
    have : φ = colim.map α ≫ e.hom := by
      refine colimit.hom_ext fun j ↦ ?_
      simp [φ, e, α]
    rw [this]
    infer_instance
  have hepi : Epi φ := by
    have : Sheaf.IsLocallySurjective φ := by
      refine ⟨fun {V} s ↦ ?_⟩
      obtain ⟨R, hR, hRs⟩ := h V s
      refine X.smallEtaleTopology.superset_covering ?_ hR
      intro W g hg
      obtain ⟨j, t, ht⟩ := hRs g hg
      refine ⟨(colimit.ι D j).hom.app (op W) t, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, colimit.ι_desc]
      exact ht
    exact Sheaf.epi_of_isLocallySurjective _
  have : IsIso ((colimit.isColimit D).desc c) := isIso_of_mono_of_epi φ
  exact IsColimit.ofPointIso (colimit.isColimit D)

/-- **Reduction to bounded exponent.** On a quasi-compact quasi-separated scheme, a torsion
sheaf is the filtered union of its `n!`-torsion subsheaves, and étale cohomology commutes with
filtered colimits; so if `Hᵠ` vanishes for sheaves killed by a positive integer, it vanishes for
torsion sheaves. -/
theorem Etale.subsingleton_H_of_isTorsion [CompactSpace X] [QuasiSeparatedSpace X]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : F.IsTorsion) (q : ℕ)
    (h : ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ), 0 < n →
      n • 𝟙 G = 0 → Subsingleton (Sheaf.H G q)) :
    Subsingleton (Sheaf.H F q) := by
  let N (n : ULift.{u} ℕ) : ℕ := (n.down + 1).factorial
  have hdvd {n m : ULift.{u} ℕ} (hnm : n ≤ m) : N n ∣ N m :=
    Nat.factorial_dvd_factorial (Nat.succ_le_succ hnm)
  let K (n : ULift.{u} ℕ) := kernel (N n • 𝟙 F)
  have hK {n m : ULift.{u} ℕ} (hnm : n ≤ m) : kernel.ι (N n • 𝟙 F) ≫ (N m • 𝟙 F) = 0 := by
    obtain ⟨c, hc⟩ := hdvd hnm
    have h0 : N n • kernel.ι (N n • 𝟙 F) = 0 := by
      rw [← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul, kernel.condition]
    rw [hc, Preadditive.comp_nsmul, Category.comp_id, mul_comm, ← smul_smul, h0, smul_zero]
  let D : ULift.{u} ℕ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    { obj := K
      map {n m} f := kernel.lift _ (kernel.ι _) (hK (leOfHom f))
      map_id n := by
        rw [← cancel_mono (kernel.ι _)]
        simp only [kernel.lift_ι]
        exact (Category.id_comp _).symm
      map_comp f g := by
        rw [← cancel_mono (kernel.ι _)]
        simp }
  let c : Cocone D := { pt := F, ι := { app n := kernel.ι _ } }
  have : ∀ n, Mono (c.ι.app n) := fun n ↦ inferInstanceAs (Mono (kernel.ι _))
  have hc : IsColimit c := Etale.isColimitOfMonoOfLocallySurjective c fun V s ↦ by
    obtain ⟨S, hS, hSs⟩ := hF (U := op V) s
    refine ⟨S, hS, fun W g hg ↦ ?_⟩
    obtain ⟨m, hm, hms⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hSs hg)
    refine ⟨ULift.up m, Etale.exists_kernel_ι_app_eq _ _ ?_⟩
    obtain ⟨d, hd⟩ : m ∣ (m + 1).factorial := Nat.dvd_factorial hm (Nat.le_succ m)
    have : ((sheafToPresheaf _ _).map (N (ULift.up m) • 𝟙 F)).app (op W) =
        N (ULift.up m) • 𝟙 _ := by
      rw [Functor.map_nsmul, NatTrans.app_nsmul]
      rfl
    change (((sheafToPresheaf _ _).map (N (ULift.up m) • 𝟙 F)).app (op W)) _ = 0
    rw [this]
    change (m + 1).factorial • (F.obj.map g.op s) = 0
    rw [hd, mul_nsmul', smul_comm, hms, smul_zero]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have := essentiallySmallSelf.{u + 1} (ULift.{u} ℕ)
  obtain ⟨n, y, rfl⟩ := (Scheme.H_map_isColimit_of_isFiltered_of_large X hc q).1 x
  have : Subsingleton (Sheaf.H (K n) q) := h _ (N n) (Nat.factorial_pos _) (by
    rw [← cancel_mono (kernel.ι (N n • 𝟙 F)), zero_comp, Preadditive.nsmul_comp,
      Category.id_comp, ← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul,
      kernel.condition])
  rw [Subsingleton.elim y 0, map_zero]

end Colimits

/-- **An affine open with finite complement.** A curve `C` has an affine open `U` whose complement
is a finite set of closed points: take the union of affine opens around the generic points of the
irreducible components, each avoiding the other components. -/
theorem IsCurve.exists_isAffineOpen_finite_compl (f : C ⟶ Spec (.of k)) [IsCurve f] :
    ∃ U : C.Opens, IsAffineOpen U ∧ (U : Set C)ᶜ.Finite ∧ ∀ x ∉ U, IsClosed ({x} : Set C) := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C := {}
  have hdim : topologicalKrullDim C ≤ 1 := IsCurve.krullDim_le_one (f := f)
  let ι := ↥(irreducibleComponents C)
  have : Finite ι := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hirr (Z : ι) : IsIrreducible Z.1 := Z.2.1
  have hcl (Z : ι) : IsClosed Z.1 := isClosed_of_mem_irreducibleComponents _ Z.2
  -- every point lies on an irreducible component
  have hmem (x : C) : ∃ Z : ι, x ∈ Z.1 := by
    obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
      isIrreducible_singleton
    exact ⟨⟨Z, hZ⟩, hxZ rfl⟩
  -- the generic points of the components
  choose ξ hξ using fun Z : ι ↦ QuasiSober.sober (hirr Z) (hcl Z)
  -- the open set of points lying on no other component
  let O (Z : ι) : C.Opens := ⟨⋂ Z' ∈ ({Z}ᶜ : Set ι), Z'.1ᶜ,
    (Set.toFinite _).isOpen_biInter fun Z' _ ↦ (hcl Z').isOpen_compl⟩
  have hO (Z Z' : ι) (x : C) (hx : x ∈ O Z) (hx' : x ∈ Z'.1) : Z' = Z := by
    by_contra h
    exact (Set.mem_iInter₂.1 hx Z' h) hx'
  have hξO (Z : ι) : ξ Z ∈ O Z := by
    refine Set.mem_iInter₂.2 fun Z' hZ' hξZ' ↦ hZ' ?_
    have hsub : Z.1 ⊆ Z'.1 := by
      rw [← (hξ Z).def]
      exact closure_minimal (Set.singleton_subset_iff.2 hξZ') (hcl Z')
    exact (Subtype.ext (Z.2.eq_of_le (hirr Z') hsub)).symm
  -- affine opens around the generic points, inside `O Z`
  choose V hV using fun Z : ι ↦
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens) (hξO Z)
  have hdisj : Pairwise (Function.onFun Disjoint V) := by
    intro Z Z' hZZ'
    rw [Function.onFun, disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨Z'', hZ''⟩ := hmem x
    exact (hZZ' ((hO Z Z'' x ((hV Z).2.2 hx.1) hZ'').symm.trans
      (hO Z' Z'' x ((hV Z').2.2 hx.2) hZ''))).elim
  let U := ⨆ Z, V Z
  refine ⟨U, IsAffineOpen.iSup_of_disjoint (fun Z ↦ (hV Z).1) hdisj, ?_⟩
  -- the complement, component by component
  have hcomp (Z : ι) : ∃ T : Set C, T.Finite ∧ (∀ x ∈ T, IsClosed ({x} : Set C)) ∧
      ∀ x ∈ Z.1, x ∉ V Z → x ∈ T := by
    have : IrreducibleSpace Z.1 := Subtype.irreducibleSpace (hirr Z)
    have : QuasiSober Z.1 := (hcl Z).isClosedEmbedding_subtypeVal.quasiSober
    have hdimZ : topologicalKrullDim Z.1 ≤ 1 :=
      IsInducing.subtypeVal.topologicalKrullDim_le.trans hdim
    let A : Set Z.1 := Subtype.val ⁻¹' (V Z : Set C)
    have hA : IsOpen A := (V Z).isOpen.preimage continuous_subtype_val
    have hAne : A.Nonempty := ⟨⟨ξ Z, (hξ Z).mem⟩, (hV Z).2.1⟩
    refine ⟨Subtype.val '' Aᶜ, (hA.finite_compl_of_topologicalKrullDim_le_one hdimZ hAne).image _,
      ?_, fun x hx hxV ↦ ⟨⟨x, hx⟩, hxV, rfl⟩⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [← Set.image_singleton]
    exact (hcl Z).isClosedEmbedding_subtypeVal.isClosedMap _
      (hA.isClosed_singleton_of_mem_compl hdimZ hAne hz)
  choose T hTfin hTcl hT using hcomp
  have hsub : (U : Set C)ᶜ ⊆ ⋃ Z, T Z := by
    intro x hx
    obtain ⟨Z, hZ⟩ := hmem x
    refine Set.mem_iUnion.2 ⟨Z, hT Z x hZ fun hxV ↦ hx ?_⟩
    exact (le_iSup V Z) hxV
  refine ⟨(Set.finite_iUnion hTfin).subset hsub, fun x hx ↦ ?_⟩
  obtain ⟨Z, hxZ⟩ := Set.mem_iUnion.1 (hsub hx)
  exact hTcl Z x hxZ

/-- A scheme which is affine and étale over an open subscheme of a curve is an affine curve. -/
lemma IsCurve.of_etale_of_isAffine (f : C ⟶ Spec (.of k)) [IsCurve f] (U : C.Opens)
    {W : Scheme.{u}} (w : W ⟶ U) [AlgebraicGeometry.Etale w] [IsAffine W] :
    IsCurve (w ≫ U.ι ≫ f) where
  krullDim_le_one :=
    ((topologicalKrullDim_le_of_continuous w.continuous fun _ _ ↦
      w.eq_of_specializes_of_apply_eq).trans
        U.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans
          (IsCurve.krullDim_le_one (f := f))

/-- The cokernel of a morphism into a sheaf killed by `n` is killed by `n`. -/
lemma Etale.nsmul_id_cokernel_eq_zero {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) {n : ℕ}
    (hG : n • 𝟙 G = 0) : n • 𝟙 (cokernel φ) = 0 := by
  rw [← cancel_epi (cokernel.π φ), comp_zero, Preadditive.comp_nsmul, Category.comp_id,
    ← Category.id_comp (cokernel.π φ), ← Preadditive.nsmul_comp, hG, zero_comp]

/-- **Vanishing in degrees at least three, reduction to affine curves.** Let `C` be a curve over
an algebraically closed field `k`, and assume that `H²` of torsion sheaves vanishes on affine
curves over `k`. Then `Hᵠ(C, F) = 0` for every torsion sheaf `F` on `C` and `q ≥ 3`. -/
theorem IsCurve.subsingleton_sheafH_of_three_le_of_forall [IsAlgClosed k]
    (f : C ⟶ Spec (.of k)) [IsCurve f]
    (H : ∀ (C' : Scheme.{u}) (f' : C' ⟶ Spec (.of k)), IsCurve f' → IsAffine C' →
      ∀ F' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1}, F'.IsTorsion →
        Subsingleton (Sheaf.H F' 2))
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 3 ≤ q) : Subsingleton (Sheaf.H F q) := by
  obtain ⟨U, hUaff, hUfin, hUcl⟩ := IsCurve.exists_isAffineOpen_finite_compl f
  have : IsAffine U := hUaff
  have hsep (x : C) (hx : x ∉ U) : IsSepClosed (C.residueField x) :=
    have := Scheme.isAlgClosed_residueField_of_isClosed f x (hUcl x hx)
    inferInstance
  let j := U.ι
  have : IsAffineHom j :=
    MorphismProperty.HasOfPostcompProperty.of_postcomp (W := @IsAffineHom)
      (W' := @IsSeparated) j f inferInstance inferInstance
  have hUcurve : IsCurve (U.ι ≫ f) := by
    simpa using IsCurve.of_etale_of_isAffine f U (𝟙 (U : Scheme.{u}))
  -- `H³` vanishes for sheaves killed by `n`
  have h3 (n : ℕ) (hn : n ≠ 0) (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : n • 𝟙 F = 0) : Subsingleton (Sheaf.H F 3) := by
    let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j
    let G := (j)^*[AddCommGrpCat.{u + 1}].obj F
    -- `H³(C, F) ≅ H³(C, j_* G)`
    have hunit : IsIso ((U.ι)^*[AddCommGrpCat.{u + 1}].map (adj.unit.app F)) := by
      have : IsIso ((j)^*[AddCommGrpCat.{u + 1}].map (adj.unit.app F) ≫ adj.counit.app G) := by
        rw [adj.left_triangle_components F]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app G)
    have hb := Etale.bijective_H_map_of_isIso_upperStar_map U hUfin hUcl hsep (adj.unit.app F)
      hunit 1
    suffices hs : Subsingleton (Sheaf.H ((j)_*[AddCommGrpCat.{u + 1}].obj G) 3) by
      have : Subsingleton (Sheaf.H (((j)^*[AddCommGrpCat.{u + 1}] ⋙
        (j)_*[AddCommGrpCat.{u + 1}]).obj F) (1 + 2)) := hs
      exact hb.injective.subsingleton
    have hG : n • 𝟙 G = 0 := by
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hF, Functor.map_zero]
    -- the two acyclic envelopes
    obtain ⟨J, ι, hι, hJn, hJ0, hJ1, hJ2⟩ :=
      Etale.exists_mono_acyclic_of_nsmul_eq_zero U hn G hG
    let S₁ := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS₁ : S₁.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) hι inferInstance
    have hG' : n • 𝟙 S₁.X₃ = 0 := Etale.nsmul_id_cokernel_eq_zero ι hJn
    obtain ⟨J', ι', hι', hJ'n, hJ'0, hJ'1, hJ'2⟩ :=
      Etale.exists_mono_acyclic_of_nsmul_eq_zero U hn S₁.X₃ hG'
    let S₂ := ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')
    have hS₂ : S₂.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) hι' inferInstance
    have hG'' : n • 𝟙 S₂.X₃ = 0 := Etale.nsmul_id_cokernel_eq_zero ι' hJ'n
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    -- `H¹(U, G'') = 0`
    have hc : Subsingleton (Sheaf.H S₂.X₃ 1) := by
      have : Subsingleton (Sheaf.H S₂.X₂ 1) := hJ'0 0
      have : Subsingleton (Sheaf.H S₂.X₁ 2) :=
        H _ _ hUcurve inferInstance _ (Scheme.isTorsion_of_nsmul_id_eq_zero hnpos hG')
      exact Sheaf.H.subsingleton_X₃_of_shortExact hS₂ 1
    -- `H¹(C, j_* G'') = 0`, as it injects into `H¹(U, G'')`
    have hd : Subsingleton (Sheaf.H ((j)_*[AddCommGrpCat.{u + 1}].obj S₂.X₃) 1) :=
      have : Subsingleton (Sheaf.H ((𝟭 (Sheaf (U : Scheme.{u}).smallEtaleTopology
        AddCommGrpCat.{u + 1})).obj S₂.X₃) 1) := hc
      (Etale.injective_edgeMap_one j S₂.X₃).subsingleton
    -- `j_* J' ⟶ j_* G''` is an epimorphism: sections over affine étale `C`-schemes lift
    have he : Epi ((j)_*[AddCommGrpCat.{u + 1}].map S₂.g) := by
      have : Sheaf.IsLocallySurjective ((j)_*[AddCommGrpCat.{u + 1}].map S₂.g) := by
        refine ⟨fun {V} s ↦ (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_⟩
        obtain ⟨A, hA, hxA, -⟩ : ∃ A : V.left.Opens, A ∈ V.left.affineOpens ∧ x ∈ A ∧ A ≤ ⊤ :=
          (TopologicalSpace.Opens.isBasis_iff_nbhd.1
          V.left.isBasis_affineOpens) (TopologicalSpace.Opens.mem_top x)
        have : IsAffine A := hA
        let VA : C.Etale := MorphismProperty.Over.mk ⊤ (A.ι ≫ V.hom)
          (MorphismProperty.comp_mem _ _ _ inferInstance V.prop)
        let g : VA ⟶ V := MorphismProperty.Over.homMk A.ι rfl trivial
        refine ⟨VA, g, ?_, ⟨x, hxA⟩, rfl⟩
        -- the base change of `VA` to `U`
        let W := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ j).obj VA
        have : IsAffine W.left := inferInstanceAs (IsAffine (pullback (A.ι ≫ V.hom) j))
        have : IsAffine ((𝟭 Scheme.{u}).obj W.left) := this
        have : AlgebraicGeometry.Etale W.hom := W.prop
        have : Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj S₂.X₁) 1) := by
          let P := (W.hom)^*[AddCommGrpCat.{u + 1}]
          have hS₁' := hS₁.map_of_exact P
          have : Subsingleton (Sheaf.H (S₁.map P).X₂ 1) := hJ2 W.hom 0
          have : Subsingleton (Sheaf.H (S₁.map P).X₁ 2) :=
            H _ _ (IsCurve.of_etale_of_isAffine f U W.hom) inferInstance _
              (Etale.isTorsion_upperStar _ (Scheme.isTorsion_of_nsmul_id_eq_zero hnpos hG))
          exact Sheaf.H.subsingleton_X₃_of_shortExact hS₁' 1
        obtain ⟨t, ht⟩ := Etale.surjective_app_of_subsingleton_H_one hS₂ W
          (((j)_*[AddCommGrpCat.{u + 1}].obj S₂.X₃).obj.map g.op s)
        exact ⟨t, ht⟩
      exact Sheaf.epi_of_isLocallySurjective _
    -- `H²(C, j_* G') = 0`
    let P := (j)_*[AddCommGrpCat.{u + 1}]
    have hS₂j : (S₂.map P).ShortExact :=
      { exact := hS₂.exact.map_of_mono_of_preservesKernel _ hS₂.mono_f inferInstance
        mono_f := inferInstanceAs (Mono (P.map S₂.f))
        epi_g := he }
    have hh : Subsingleton (Sheaf.H (P.obj S₁.X₃) 2) := by
      have : Subsingleton (Sheaf.H (S₂.map P).X₃ 1) := hd
      have : Subsingleton (Sheaf.H (S₂.map P).X₂ 2) := hJ'1 j 1
      exact Sheaf.H.subsingleton_X₁_of_shortExact hS₂j 1
    -- the cokernel of `j_* J ⟶ j_* G'`, and the comparison with `j_* G'`
    let T := S₁.map P
    have hT : T.Exact := hS₁.exact.map_of_mono_of_preservesKernel _ hS₁.mono_f inferInstance
    have : Mono T.f := inferInstanceAs (Mono (P.map S₁.f))
    let ψ := cokernel.desc T.f T.g T.zero
    have : Mono ψ := hT.mono_cokernelDesc
    let Sa := ShortComplex.mk T.f (cokernel.π T.f) (cokernel.condition _)
    have hSa : Sa.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    let Sb := ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition _)
    have hSb : Sb.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    -- the cokernel of `ψ` vanishes over `U`
    have hR : IsZero ((U.ι)^*[AddCommGrpCat.{u + 1}].obj (cokernel ψ)) := by
      let Q := (j)^*[AddCommGrpCat.{u + 1}]
      have h₁ : Epi (Q.map T.g) := by
        have h : Q.map T.g ≫ adj.counit.app S₁.X₃ = adj.counit.app S₁.X₂ ≫ S₁.g :=
          adj.counit.naturality S₁.g
        have : Epi (Q.map T.g ≫ adj.counit.app S₁.X₃) := by
          rw [h]
          infer_instance
        have h' : Q.map T.g = (Q.map T.g ≫ adj.counit.app S₁.X₃) ≫
            inv (adj.counit.app S₁.X₃) := by simp
        rw [h']
        infer_instance
      have : Epi (Q.map ψ) := by
        have : Q.map (cokernel.π T.f) ≫ Q.map ψ = Q.map T.g := by
          rw [← Q.map_comp, cokernel.π_desc]
        exact epi_of_epi_fac this
      exact (isZero_cokernel_of_epi (Q.map ψ)).of_iso (PreservesCokernel.iso Q ψ)
    have hRa (i : ℕ) : Subsingleton (Sheaf.H (cokernel ψ) (i + 1)) :=
      Etale.subsingleton_H_of_isZero_upperStar U hUfin hUcl hsep _ hR i
    have hN : Subsingleton (Sheaf.H (cokernel T.f) 2) := by
      have : Subsingleton (Sheaf.H Sb.X₃ 1) := hRa 0
      have : Subsingleton (Sheaf.H Sb.X₂ 2) := hh
      exact Sheaf.H.subsingleton_X₁_of_shortExact hSb 1
    have : Subsingleton (Sheaf.H Sa.X₃ 2) := hN
    have : Subsingleton (Sheaf.H Sa.X₂ 3) := hJ1 j 2
    exact Sheaf.H.subsingleton_X₁_of_shortExact hSa 2
  -- all degrees `q ≥ 3` for sheaves killed by some `n`, by dimension shifting on `C`
  have hbdd (q : ℕ) : ∀ (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ),
      0 < n → n • 𝟙 G = 0 → Subsingleton (Sheaf.H G (3 + q)) := by
    induction q with
    | zero => exact fun G n hn hG ↦ h3 n hn.ne' G hG
    | succ q ih =>
      intro G n hn hG
      obtain ⟨J, ι, hι, hJn, hJ0, -, -⟩ := Etale.exists_mono_acyclic_of_nsmul_eq_zero C hn.ne' G hG
      let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) hι inferInstance
      have : Subsingleton (Sheaf.H S.X₃ (3 + q)) :=
        ih _ n hn (Etale.nsmul_id_cokernel_eq_zero ι hJn)
      have : Subsingleton (Sheaf.H S.X₂ (3 + q + 1)) := hJ0 _
      exact Sheaf.H.subsingleton_X₁_of_shortExact hS (3 + q)
  -- torsion sheaves are filtered unions of sheaves killed by some `n`
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian C := {}
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hq
  exact Etale.subsingleton_H_of_isTorsion hF _ (hbdd q)

end AlgebraicGeometry
