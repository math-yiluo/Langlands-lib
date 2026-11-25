/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport
public import WeilConjectures.WeilSheaf.DenseOpen
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil

/-!
# The unit of a dense open of the affine line

Let `j : U₀ ↪ 𝔸¹` be a dense open immersion. For a Weil sheaf `G` on the affine line, the unit
`G ⟶ j_* j^* G` becomes an isomorphism on `U₀`, so its kernel and cokernel are punctual. These
facts, and the restriction of an irreducible lisse sheaf to a smaller dense open, are the
sheaf-theoretic input of the description of the simple curve perverse sheaves (blueprint
`lemma-simple-objects--1`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.mono_unit_app`: the unit `G ⟶ j_* j^* G` is a
  monomorphism when `G` has no nonzero punctual subsheaf, and its cokernel is punctual
  (`AlgebraicGeometry.WeilSheaf.support_finite_cokernel_unit_app`).
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_mono_directImage`: a Weil sheaf without
  punctual subsheaf embeds into the direct image of its restriction to a dense lisse open, with
  punctual cokernel.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_or_isZero_of_exact`: an exact sequence
  `A ↪ j_*N ⟶ B ↠ C` with `N` irreducible lisse, `C` punctual and `B` without punctual subsheaf,
  has `A = C = 0` or `B = 0`.

## Implementation notes

The open immersion `j` of a datum is separated as a monomorphism in the statements of the
adjunction `j^* ⊣ j_*`. The affine `U₀` gives a second instance, through the separatedness of
`U₀`, whose proof term differs; unifying the two statements is then very slow. We therefore raise
the priority of `AlgebraicGeometry.IsSeparated.isSeparated_of_mono` locally.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

attribute [local instance 1000] IsSeparated.isSeparated_of_mono


section DenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ affineLine k₀)
  [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

omit [Finite k₀] [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [U.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [IsOpenImmersion j] [QuasiCompact j]
  [j.IsOver (Spec (CommRingCat.of k₀))] in
/-- The source of a dominant morphism to the affine line is nonempty. -/
theorem nonempty_of_isDominant [IsDominant j] : Nonempty U :=
  j.denseRange.nonempty_iff.2
    ⟨((affineLine k₀ ↘ Spec (.of k₀)).surjective (IsLocalRing.closedPoint k₀)).choose⟩

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- The restriction `j^*` of the unit `G ⟶ j_* j^* G` of an open immersion `j : U₀ ↪ 𝔸¹` is an
isomorphism, the counit `j^* j_* ⟶ 𝟭` being one. -/
theorem isIso_upperStar_map_unit_app (G : WeilSheaf k₀ l (affineLine k₀)) :
    IsIso ((upperStar j).map ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G)) :=
  Adjunction.isIso_map_unit_app_of_isIso_counit_app _ G

/-- The kernel of the unit `G ⟶ j_* j^* G` of a dense open `j : U₀ ↪ 𝔸¹` is punctual: it
vanishes on `U₀`. -/
theorem support_finite_kernel_unit_app [IsDominant j] (G : WeilSheaf k₀ l (affineLine k₀)) :
    (kernel ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G)).support.Finite := by
  have := nonempty_of_isDominant j
  have := isIso_upperStar_map_unit_app j G
  have : Mono ((upperStar j).map ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app
      G)) :=
    IsIso.mono_of_iso _
  exact support_finite_of_isZero_upperStar j _
    ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (upperStar (k₀ := k₀) (l := l) j) _))

/-- The cokernel of the unit `G ⟶ j_* j^* G` of a dense open `j : U₀ ↪ 𝔸¹` is punctual: it
vanishes on `U₀`. -/
theorem support_finite_cokernel_unit_app [IsDominant j] (G : WeilSheaf k₀ l (affineLine k₀)) :
    (cokernel ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G)).support.Finite
    := by
  have := nonempty_of_isDominant j
  have := isIso_upperStar_map_unit_app j G
  have : Epi ((upperStar j).map ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app
      G)) :=
    IsIso.epi_of_iso _
  exact support_finite_of_isZero_upperStar j _
    ((isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso (upperStar (k₀ := k₀) (l := l) j) _))

/-- The unit `G ⟶ j_* j^* G` of a dense open `j : U₀ ↪ 𝔸¹` is a monomorphism when `G` has no
nonzero punctual subsheaf: its kernel is punctual. -/
theorem mono_unit_app [IsDominant j] {G : WeilSheaf k₀ l (affineLine k₀)}
    (hG : ∀ (G' : WeilSheaf k₀ l (affineLine k₀)) (i : G' ⟶ G), Mono i → G'.support.Finite →
      IsZero G') :
    Mono ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app G) :=
  Preadditive.mono_of_isZero_kernel _
    (hG _ (kernel.ι _) inferInstance (support_finite_kernel_unit_app j G))

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- Every morphism from a punctual Weil sheaf to the direct image `j_* N` of a lisse sheaf on a
dense open `j : U₀ ↪ 𝔸¹` vanishes
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.eq_zero_of_support_finite`). -/
theorem eq_zero_of_support_finite_lowerStar [IsDominant j] {N : WeilSheaf k₀ l U}
    (hN : N.IsLisse) {G : WeilSheaf k₀ l (affineLine k₀)} (hG : G.support.Finite)
    (i : G ⟶ (lowerStar j).obj N) : i = 0 :=
  (⟨U, j, N, hN⟩ : LisseOnDenseOpen k₀ l).eq_zero_of_support_finite hG i

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- A punctual Weil sheaf `G` on the affine line whose restriction to a dense open
`j : U₀ ↪ 𝔸¹` is lisse vanishes on `U₀`: the unit `G ⟶ j_* j^* G` is a morphism from a punctual
sheaf to the direct image of a lisse sheaf, hence zero, and its restriction to `U₀` is
invertible. -/
theorem isZero_upperStar_of_isLisse [IsDominant j] {G : WeilSheaf k₀ l (affineLine k₀)}
    (hG : G.support.Finite) (hGl : ((upperStar j).obj G).IsLisse) :
    IsZero ((upperStar j).obj G) := by
  set adj := upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j
  have h0 : adj.homEquiv _ _ (𝟙 ((upperStar j).obj G)) = adj.homEquiv _ _ 0 := by
    rw [eq_zero_of_support_finite_lowerStar j hGl hG (adj.homEquiv _ _ _), Adjunction.homEquiv_unit,
      Functor.map_zero,
      comp_zero]
  exact (IsZero.iff_id_eq_zero _).2 ((adj.homEquiv _ _).injective h0)

end DenseOpen

namespace LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (D : LisseOnDenseOpen k₀ l)

/-- A Weil sheaf on `U₀` whose direct image vanishes is zero: `j^* j_* N' ≅ N'`. -/
theorem isZero_of_isZero_lowerStar {N' : WeilSheaf k₀ l D.U}
    (h : IsZero ((lowerStar D.j).obj N')) : IsZero N' :=
  ((upperStar D.j).map_isZero h).of_iso (upperStarDirectImageIso D.j N').symm

/-- A morphism of Weil sheaves on `U₀` whose direct image is an isomorphism is an isomorphism:
`j^* j_* ≅ 𝟭`. -/
theorem isIso_of_isIso_lowerStar_map {N' N : WeilSheaf k₀ l D.U} (i : N' ⟶ N)
    (h : IsIso ((lowerStar D.j).map i)) : IsIso i := by
  have hn := (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).counit.naturality i
  have : IsIso (((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).counit.app N') ≫
      (𝟭 _).map i) := by
    have : IsIso ((lowerStar D.j ⋙ upperStar D.j).map i) :=
      Functor.map_isIso (upperStar D.j) ((lowerStar D.j).map i)
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j).counit.app N') ((𝟭 _).map i)

/-- For a lisse subsheaf `N' ⊆ N`, the cokernel of `j_* N' ⟶ j_* N` has no nonzero punctual
subsheaf: by left exactness of `j_*` it embeds into `j_*(N / N')`, the direct image of a lisse
sheaf. -/
theorem isZero_of_mono_cokernel_lowerStar_map {N' : WeilSheaf k₀ l D.U} (i : N' ⟶ D.sheaf)
    [Mono i] (hN' : N'.IsLisse) (G : WeilSheaf k₀ l (affineLine k₀))
    (g : G ⟶ cokernel ((lowerStar D.j).map i)) [Mono g] (hG : G.support.Finite) : IsZero G := by
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.Exact := ShortComplex.exact_cokernel i
  have hex := hS.map_of_mono_of_preservesKernel (lowerStar D.j) (inferInstanceAs (Mono i))
    inferInstance
  have := (ShortComplex.exact_iff_mono_cokernel_desc _).1 hex
  refine IsZero.of_mono_eq_zero g
    ((cancel_mono (cokernel.desc _ _ (S.map (lowerStar D.j)).zero)).1 ?_)
  rw [zero_comp]
  exact eq_zero_of_support_finite_lowerStar D.j (hN'.kernel_cokernel D.lisse i).2 hG _

/-- A Weil sheaf on `U₀` vanishing on a nonempty open `V ⊆ U₀` is punctual: its support lies
over the finitely many closed points of the affine line outside `V`. -/
theorem support_finite_of_isZero_upperStar_opensι (V : D.U.Opens) [Nonempty V]
    (H : WeilSheaf k₀ l D.U) (h : IsZero ((upperStar V.ι).obj H)) : H.support.Finite := by
  let f : D.U.finitePoints → (affineLine k₀).finitePoints :=
    fun y ↦ ⟨D.j.base y.1, Scheme.Hom.map_mem_finitePoints D.j y.2⟩
  have hf : Function.Injective f := fun y y' hyy' ↦
    Subtype.ext (D.j.isOpenEmbedding.injective (congrArg Subtype.val hyy'))
  refine ((affineLine.finite_setOf_notMem (V.ι ≫ D.j).isOpenEmbedding.isOpen_range
    (Set.range_nonempty _)).preimage hf.injOn).subset fun y hy hVy ↦ ?_
  obtain ⟨z, hz⟩ := hVy
  have hz' : V.ι.base z = y.1 :=
    D.j.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, hz])
  have hzf : z ∈ (V : Scheme).finitePoints :=
    Scheme.Hom.mem_finitePoints_of_isOpenImmersion V.ι (hz' ▸ y.2)
  have hmem := (mem_support_upperStar_iff V.ι H ⟨z, hzf⟩).2 (by convert hy)
  rw [support_eq_empty_of_isZero h] at hmem
  exact hmem

/-- Given finitely many closed points `S` of the affine line, the points of `U₀` lying over `S`
form a closed subset with dense complement. -/
theorem exists_dense_forall_notMem (S : Set (affineLine k₀).finitePoints) (hS : S.Finite) :
    ∃ W : D.U.Opens, Dense (W : Set D.U) ∧ ∀ y : D.U.finitePoints, y.1 ∈ W →
      (⟨D.j.base y.1, Scheme.Hom.map_mem_finitePoints D.j y.2⟩ :
        (affineLine k₀).finitePoints) ∉ S := by
  let f : D.U.finitePoints → (affineLine k₀).finitePoints :=
    fun y ↦ ⟨D.j.base y.1, Scheme.Hom.map_mem_finitePoints D.j y.2⟩
  have hf : Function.Injective f := fun y y' hyy' ↦
    Subtype.ext (D.j.isOpenEmbedding.injective (congrArg Subtype.val hyy'))
  set Z : Set D.U := ⋃ y ∈ f ⁻¹' S, {y.1}
  have hZ : IsClosed Z := (hS.preimage hf.injOn).isClosed_biUnion fun y _ ↦
    D.U.isClosed_singleton_of_mem_finitePoints y.2
  refine ⟨⟨Zᶜ, hZ.isOpen_compl⟩, hZ.isOpen_compl.dense ?_, fun y hy hyS ↦
    hy (Set.mem_biUnion (x := y) hyS rfl)⟩
  -- otherwise `U₀` is a single closed point, and so is the affine line
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hcon
  set η := genericPoint D.U
  have hηZ : η ∈ Z := hcon ▸ Set.mem_univ η
  obtain ⟨y, -, hy⟩ := Set.mem_iUnion₂.1 hηZ
  rw [Set.mem_singleton_iff] at hy
  have hη (z : D.U) : z = η := by
    have hz : z ∈ closure ({η} : Set D.U) := by
      rw [(genericPoint_spec D.U).def]
      exact Set.mem_univ z
    rwa [(D.U.isClosed_singleton_of_mem_finitePoints (hy ▸ y.2)).closure_eq] at hz
  have hcl : IsClosed ({D.j.base η} : Set (affineLine k₀)) :=
    (affineLine k₀).isClosed_singleton_of_mem_finitePoints
      (hy ▸ Scheme.Hom.map_mem_finitePoints D.j y.2)
  have hx (x : affineLine k₀) : x = D.j.base η := by
    have hx : x ∈ closure (Set.range D.j.base) := by
      rw [D.j.denseRange.closure_eq]
      exact Set.mem_univ x
    refine Set.mem_singleton_iff.1 ((closure_minimal ?_ hcl) hx)
    rintro _ ⟨z, rfl⟩
    rw [hη z]
    exact rfl
  obtain ⟨a, b, hab⟩ := affineLine.nontrivial k₀
  exact hab ((hx a).trans (hx b).symm)

/-- **Simplicity of a middle extension, sheaf part** (`lemma-simple-objects--1`). Let
`A ↪ M ⟶ B ↠ C` be an exact sequence of Weil sheaves on the affine line with `M ≅ j_*N` for an
irreducible lisse `N`, `C` punctual and `B` without nonzero punctual subsheaf. Then `A = C = 0`
or `B = 0`. Choose a dense open `k : V ↪ U₀` on which `A` and `C` are lisse; then `C|_V = 0`,
and `A|_V ⊆ N|_V` is `0` or `N|_V`, the restriction `N|_V` being irreducible
(`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.upperStar_of_isDominant`):

- if `A|_V = 0`, then `A` is a punctual subsheaf of `j_*N`, hence zero, and `M ⟶ B` is
  injective and an isomorphism on `V`. The map `θ : B ⟶ j_* k_* (B|_V)` is injective, its kernel
  being a punctual subsheaf of `B`, and `M ⟶ B ⟶ j_* k_* (B|_V)` is the isomorphism
  `M ≅ j_* k_* (M|_V) ≅ j_* k_* (B|_V)`, the unit `N ⟶ k_* k^* N` being invertible for the
  lisse `N`. So `M ⟶ B` is an isomorphism and `C = 0`;
- if `A|_V = N|_V`, then `B|_V ⊆ C|_V = 0`, so `B` is punctual, hence zero. -/
theorem isZero_or_isZero_of_exact (hD : D.sheaf.IsIrreducibleLisse)
    {A M B C : WeilSheaf k₀ l (affineLine k₀)} (eM : M ≅ D.directImage) (a : A ⟶ M) (s : M ⟶ B)
    (t : B ⟶ C) [Mono a] [Epi t] (has : a ≫ s = 0) (hst : s ≫ t = 0)
    (h₁ : (ShortComplex.mk a s has).Exact) (h₂ : (ShortComplex.mk s t hst).Exact)
    (hC : C.support.Finite)
    (hB : ∀ (G : WeilSheaf k₀ l (affineLine k₀)) (i : G ⟶ B), Mono i → G.support.Finite →
      IsZero G) :
    (IsZero A ∧ IsZero C) ∨ IsZero B := by
  let eM' : M ≅ (lowerStar D.j).obj D.sheaf :=
    eM ≪≫ (Iso.refl D.directImage : D.directImage ≅ (lowerStar D.j).obj D.sheaf)
  -- a dense open `V ⊆ U₀` on which `A` is lisse and `C` vanishes
  obtain ⟨VA, hVA, hA⟩ := exists_dense_isLisse_upperStar ((upperStar D.j).obj A)
  obtain ⟨VC, hVC, hCV⟩ := D.exists_dense_forall_notMem C.support hC
  set V : D.U.Opens := VA ⊓ VC
  have hV : Dense (V : Set D.U) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact hVA.inter_of_isOpen_left hVC VA.isOpen
  have : IsDominant V.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have : Nonempty V := hV.nonempty.to_subtype
  have hlisse (W : D.U.Opens) (hVW : V ≤ W) (G : WeilSheaf k₀ l D.U)
      (hG : ((upperStar W.ι).obj G).IsLisse) : ((upperStar V.ι).obj G).IsLisse := by
    have : (D.U.homOfLE hVW).IsOver (Spec (CommRingCat.of k₀)) :=
      ⟨by rw [← comp_over W.ι, Scheme.homOfLE_ι_assoc, comp_over V.ι]⟩
    exact (isLisse_upperStar_congr (Scheme.homOfLE_ι _ hVW) _).1
      ((isLisse_upperStar_comp_iff _ W.ι _).2 (hG.upperStar _))
  -- the restriction `ρ = k^* j^*` to `V`
  set ρ := upperStar (k₀ := k₀) (l := l) D.j ⋙ upperStar V.ι
  have eρ (G : WeilSheaf k₀ l (affineLine k₀)) :
      ρ.obj G ≅ (upperStar V.ι).obj ((upperStar D.j).obj G) :=
    eqToIso (Functor.comp_obj _ _ G)
  -- a sheaf vanishing on `V` is punctual
  have hpunct (G : WeilSheaf k₀ l (affineLine k₀)) (h : IsZero (ρ.obj G)) : G.support.Finite :=
    have := D.nonempty_U
    support_finite_of_support_upperStar_finite D.j G
      (D.support_finite_of_isZero_upperStar_opensι V _ (h.of_iso (eρ G).symm))
  have hC0 : IsZero (ρ.obj C) := by
    refine (isZero_upperStar_of_forall_notMem_support V.ι _ fun y hy ↦ ?_).of_iso (eρ C)
    rw [mem_support_upperStar_iff] at hy
    exact hCV ⟨_, _⟩ y.1.2.2 hy
  -- `s` is an epimorphism on `V`, its cokernel `C` vanishing there
  have : Epi t := inferInstance
  have eC : cokernel s ≅ C :=
    (cokernelIsCokernel s).coconePointUniqueUpToIso h₂.gIsCokernel
  have hρs : Epi (ρ.map s) := Preadditive.epi_of_isZero_cokernel _
    ((hC0.of_iso (ρ.mapIso eC)).of_iso (PreservesCokernel.iso ρ s).symm)
  have : Mono (ρ.map a) := ρ.map_mono a
  let E : ρ.obj M ≅ (upperStar V.ι).obj D.sheaf :=
    ρ.mapIso eM' ≪≫ eρ _ ≪≫ (upperStar V.ι).mapIso (upperStarDirectImageIso D.j D.sheaf)
  have hm : Mono (ρ.map a ≫ E.hom) := @mono_comp _ _ _ _ _ _ _ _ (IsIso.mono_of_iso _)
  -- the restriction of `a` to `V`, a lisse subsheaf of `N|_V`
  obtain h | h := (hD.upperStar_of_isDominant V.ι).2.2 _
    (ρ.map a ≫ E.hom) hm ((hlisse VA inf_le_left _ hA).of_iso (eρ A).symm)
  · left
    have hA0 : IsZero A := by
      have h0 := D.eq_zero_of_support_finite (hpunct A h) (a ≫ eM.hom)
      exact IsZero.of_mono_eq_zero a ((cancel_mono eM.hom).1 (h0.trans zero_comp.symm))
    have : Mono s := h₁.mono_g (hA0.eq_of_src _ _)
    have : Mono (ρ.map s) := ρ.map_mono s
    have hρs : IsIso (ρ.map s) := isIso_of_mono_of_epi _
    rw [Functor.comp_map] at hρs
    set adj := upperStarLowerStarAdjunction (k₀ := k₀) (l := l) D.j
    set adjV := upperStarLowerStarAdjunction (k₀ := k₀) (l := l) V.ι
    -- `θ : B ⟶ j_* k_* (B|_V)`, adjoint to the identity of `B|_V`
    obtain ⟨u, hu⟩ : ∃ u, u = adjV.homEquiv _ _ (𝟙 ((upperStar V.ι).obj ((upperStar D.j).obj B))) :=
      ⟨_, rfl⟩
    obtain ⟨θ, hθ⟩ : ∃ θ, θ = adj.homEquiv _ _ u := ⟨_, rfl⟩
    -- `θ` is an isomorphism on `V`
    have hVu : IsIso ((upperStar V.ι).map u) := by
      have h := adjV.homEquiv_counit (g := u)
      rw [hu, Equiv.symm_apply_apply, ← hu] at h
      have : IsIso ((upperStar V.ι).map u ≫ adjV.counit.app _) := by
        rw [← h]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (adjV.counit.app _)
    have hρθ : IsIso (ρ.map θ) := by
      have h := adj.homEquiv_counit (g := θ)
      rw [hθ, Equiv.symm_apply_apply, ← hθ] at h
      have h2 := h ▸ hVu
      rw [Functor.map_comp] at h2
      rw [Functor.comp_map]
      exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance h2
    -- `θ` is injective: its kernel vanishes on `V`
    have : Mono θ := by
      refine Preadditive.mono_of_isZero_kernel _ (hB _ (kernel.ι _) inferInstance (hpunct _ ?_))
      have := @IsIso.mono_of_iso _ _ _ _ _ hρθ
      exact (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso ρ θ)
    -- `s ≫ θ` is an isomorphism
    have : IsIso (adj.unit.app M) := (adj.isIso_unit_app_iff_of_iso_obj eM').2
      (Adjunction.isIso_unit_app_obj_of_isIso_counit_app adj D.sheaf)
    have : IsIso (adjV.unit.app ((upperStar D.j).obj M)) :=
      (D.lisse.of_iso ((upperStar D.j).mapIso eM' ≪≫ upperStarDirectImageIso D.j D.sheaf).symm
        ).isIso_upperStarLowerStarAdjunction_unit_app V.ι (by rwa [Scheme.Opens.range_ι])
    have : IsIso (s ≫ θ) := by
      rw [hθ, hu, ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left,
        Category.comp_id, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      infer_instance
    have : Epi θ := epi_of_epi s θ
    have : IsIso θ := isIso_of_mono_of_epi θ
    have : IsIso s := IsIso.of_isIso_comp_right s θ
    refine ⟨hA0, IsZero.of_epi_eq_zero t ?_⟩
    rw [← cancel_epi s, hst, comp_zero]
  · right
    have : IsIso (ρ.map a) := IsIso.of_isIso_comp_right _ E.hom
    have hs : ρ.map s = 0 := by
      rw [← cancel_epi (ρ.map a), ← Functor.map_comp, has, Functor.map_zero, comp_zero]
    exact hB B (𝟙 B) inferInstance (hpunct B (IsZero.of_epi_eq_zero _ hs))
end LisseOnDenseOpen

/-- **Embedding into a middle extension.** A Weil sheaf `F` on the affine line without nonzero
punctual subsheaf embeds into the direct image `j_* N` of its restriction `N` to a dense open
`j : U₀ ↪ 𝔸¹` on which it is lisse, with punctual cokernel: the kernel and the cokernel of the
unit `F ⟶ j_* j^* F` vanish on `U₀`. (blueprint: `lemma-simple-objects--1`) -/
theorem LisseOnDenseOpen.exists_mono_directImage {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {F : WeilSheaf k₀ l (affineLine k₀)}
    (hF : ∀ (G : WeilSheaf k₀ l (affineLine k₀)) (i : G ⟶ F), Mono i → G.support.Finite →
      IsZero G) :
    ∃ (D : LisseOnDenseOpen k₀ l) (η : F ⟶ D.directImage), Mono η ∧
      (cokernel η).support.Finite := by
  have : IsNoetherian (affineLine k₀) :=
    isNoetherian_of_locallyOfFiniteType (affineLine k₀ ↘ Spec (.of k₀))
  obtain ⟨U, hU, hUl⟩ := exists_dense_isLisse_upperStar F
  have : IsDominant U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  exact ⟨⟨U, U.ι, (upperStar U.ι).obj F, hUl⟩, _, mono_unit_app U.ι hF,
    support_finite_cokernel_unit_app U.ι F⟩

end WeilSheaf

end AlgebraicGeometry
