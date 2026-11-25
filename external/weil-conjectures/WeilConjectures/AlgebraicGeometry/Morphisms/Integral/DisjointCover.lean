/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceRefine
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.RingTheory.Ideal.GoingUp

/-!
# Étale coverings of the base change of an integral morphism

Let `f : X ⟶ Y` be an integral morphism, `y : Spec Ω ⟶ Y` a geometric point with `Ω`
algebraically closed, and `(U, u)` a pointed étale neighbourhood of `y`. Every étale covering of
`U ×_Y X` becomes, after passing to a smaller pointed étale neighbourhood `(U', u')` of `y`,
refined by a decomposition of `U' ×_Y X` into pairwise disjoint open subschemes
(`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_hom_disjoint_cover`).

For a finite morphism this is the statement that the pieces of a split neighbourhood refine
every étale covering (`AlgebraicGeometry.Scheme.Hom.SplitNbhd.exists_forall_exists_pieceObj_hom`).
The integral case is reduced to it by a limit argument: for `U = Spec A` affine,
`U ×_Y X = Spec B` with `B` integral over `A`; finitely many standard étale `B`-algebras refine
the covering, they descend to a subalgebra `B'` of `B` finite over `A`
(`StandardEtalePair.exists_subalgebra_finite_algEquiv_tensor_ring`), their spectra still cover
`Spec B'` by lying over (`PrimeSpectrum.exists_comap_eq_of_isIntegral_of_tensor`), and the
pieces of a split neighbourhood for the finite morphism `Spec B' ⟶ U` pull back to the required
decomposition of `U' ×_Y X`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom.Nbhd

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] {y : Spec (.of Ω) ⟶ Y}

/-- The marked point of a pointed étale neighbourhood `(U, u)`, as a point of an open `U₁` of
`U` containing it. -/
def restrictPt (c : Nbhd y) (U₁ : c.1.left.Opens)
    (hU₁ : c.2.left (default : Spec (.of Ω)) ∈ U₁) : Spec (.of Ω) ⟶ U₁ :=
  IsOpenImmersion.lift U₁.ι c.2.left (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of Ω)) p default]
    exact hU₁)

@[reassoc (attr := simp)]
lemma restrictPt_ι (c : Nbhd y) (U₁ : c.1.left.Opens)
    (hU₁ : c.2.left (default : Spec (.of Ω)) ∈ U₁) :
    c.restrictPt U₁ hU₁ ≫ U₁.ι = c.2.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The pointed étale neighbourhood of `y` given by an open `U₁` of a pointed étale
neighbourhood `(U, u)` containing the marked point. -/
abbrev restrict (c : Nbhd y) (U₁ : c.1.left.Opens)
    (hU₁ : c.2.left (default : Spec (.of Ω)) ∈ U₁) : Nbhd y :=
  Functor.elementsMk _ (Scheme.Etale.mk (U₁.ι ≫ c.1.hom))
    (CategoryTheory.Over.homMk (c.restrictPt U₁ hU₁) (by
      change c.restrictPt U₁ hU₁ ≫ U₁.ι ≫ c.1.hom = y
      rw [restrictPt_ι_assoc]
      exact CategoryTheory.Over.w c.2))

/-- The inclusion of the restriction of a pointed étale neighbourhood to an open. -/
def restrictHom (c : Nbhd y) (U₁ : c.1.left.Opens)
    (hU₁ : c.2.left (default : Spec (.of Ω)) ∈ U₁) : c.restrict U₁ hU₁ ⟶ c :=
  Functor.Elements.homMk (MorphismProperty.Over.homMk U₁.ι rfl)
    (CategoryTheory.Over.OverMorphism.ext (c.restrictPt_ι U₁ hU₁))

/-- A pointed étale neighbourhood of the point `u` of a pointed étale neighbourhood `(U, u)` of
`y`, seen as a pointed étale neighbourhood of `y`. -/
abbrev comp (c : Nbhd y) (d : Nbhd c.2.left) : Nbhd y :=
  Functor.elementsMk _ (Scheme.Etale.mk (d.1.hom ≫ c.1.hom))
    (CategoryTheory.Over.homMk d.2.left (by
      have h₁ : d.2.left ≫ d.1.hom = c.2.left := CategoryTheory.Over.w d.2
      have h₂ : c.2.left ≫ c.1.hom = y := CategoryTheory.Over.w c.2
      change d.2.left ≫ d.1.hom ≫ c.1.hom = y
      rw [← Category.assoc, h₁, h₂]))

/-- The structure morphism `c.comp d ⟶ c`. -/
def compHom (c : Nbhd y) (d : Nbhd c.2.left) : c.comp d ⟶ c :=
  Functor.Elements.homMk (MorphismProperty.Over.homMk d.1.hom rfl)
    (CategoryTheory.Over.OverMorphism.ext (CategoryTheory.Over.w d.2))

@[simp]
lemma compHom_val_left (c : Nbhd y) (d : Nbhd c.2.left) :
    (c.compHom d).val.left = d.1.hom :=
  rfl

/-- An open `P` of the base change `U ×_Y X`, as an étale `X`-scheme. -/
abbrev openObj (f : X ⟶ Y) (c : Nbhd y) (P : (pullback c.1.hom f).Opens) : X.Etale :=
  Scheme.Etale.mk (P.ι ≫ pullback.snd c.1.hom f)

/-- The inclusion of an open `P` of the base change `U ×_Y X`, as a morphism of étale
`X`-schemes. -/
def openIncl (f : X ⟶ Y) (c : Nbhd y) (P : (pullback c.1.hom f).Opens) :
    openObj f c P ⟶ f.Etale.obj c.1 :=
  MorphismProperty.Over.homMk P.ι rfl

@[simp]
lemma openIncl_left (f : X ⟶ Y) (c : Nbhd y) (P : (pullback c.1.hom f).Opens) :
    (openIncl f c P).left = P.ι :=
  rfl

instance (f : X ⟶ Y) (c : Nbhd y) (P : (pullback c.1.hom f).Opens) :
    Mono (openIncl f c P) where
  right_cancellation g h hgh := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono P.ι).mp
    exact congrArg (fun m ↦ m.left) hgh

variable (f : X ⟶ Y) [IsIntegralHom f] [IsAlgClosed Ω]

/-- The affine case of `AlgebraicGeometry.Scheme.Hom.Nbhd.exists_hom_disjoint_cover`. -/
theorem exists_hom_disjoint_cover_of_isAffine (c : Nbhd y) [IsAffine c.1.left]
    (R : Sieve (f.Etale.obj c.1)) (hR : R ∈ X.smallEtaleTopology _) :
    ∃ (c' : Nbhd y) (g : c' ⟶ c) (ι : Type u) (P : ι → (pullback c'.1.hom f).Opens),
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧ ⨆ i, P i = ⊤ ∧
        ∀ i, R (openIncl f c' (P i) ≫ f.Etale.map g.val) := by
  classical
  have : IsAffine ((𝟭 Scheme).obj c.1.left) := ‹IsAffine c.1.left›
  have : IsAffine (pullback c.1.hom f) := isAffine_of_isAffineHom (pullback.fst c.1.hom f)
  -- `U = Spec A` and `U ×_Y X = Spec B` with `B` integral over `A`
  let A := Γ(c.1.left, ⊤)
  let B := Γ(pullback c.1.hom f, ⊤)
  let _ : Algebra A B := (pullback.fst c.1.hom f).appTop.hom.toAlgebra
  have : Algebra.IsIntegral A B := ⟨fun b ↦
    ((HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)).mp
      (inferInstance : IsIntegralHom (pullback.fst c.1.hom f))).2 b⟩
  -- finitely many standard étale `B`-algebras refining `R`
  have h₁ (x : ↥(pullback c.1.hom f)) : ∃ (V : X.Etale) (g : V ⟶ f.Etale.obj c.1) (_ : R g)
      (P : StandardEtalePair B) (e : Spec (.of P.Ring) ⟶ V.left),
      e ≫ g.left ≫ (pullback c.1.hom f).isoSpec.hom =
        Spec.map (CommRingCat.ofHom (algebraMap B P.Ring)) ∧
      (pullback c.1.hom f).isoSpec.hom x ∈
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap B P.Ring))) := by
    obtain ⟨V, g, hg, w, hw⟩ := (mem_smallEtaleTopology_iff R).mp hR x
    obtain ⟨P, e, he, v, hv⟩ :=
      Etale.exists_standardEtalePair (g.left ≫ (pullback c.1.hom f).isoSpec.hom) w
    refine ⟨V, g, hg, P, e, he, v, ?_⟩
    rw [← he, Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply, hw]
    rfl
  choose V g hg P e he hx using h₁
  have hPet (x) :
      AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap B (P x).Ring))) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale B (P x).Ring)))
  -- by quasi-compactness, finitely many of them cover `Spec B`
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ Set.range (Spec.map (CommRingCat.ofHom (algebraMap B (P x).Ring))))
    (fun x ↦ (Spec.map (CommRingCat.ofHom (algebraMap B (P x).Ring))).isOpenMap.isOpen_range)
    (fun p _ ↦ Set.mem_iUnion.mpr ⟨(pullback c.1.hom f).isoSpec.inv p, by
      simpa using hx ((pullback c.1.hom f).isoSpec.inv p)⟩)
  -- they descend to a subalgebra `B'` of `B` finite over `A`
  obtain ⟨B', hB', Q, hQ⟩ := StandardEtalePair.exists_subalgebra_finite_algEquiv_tensor_ring
    (A := A) (B := B) (fun x : s ↦ P x.1)
  let E (x : s) := (hQ x).some
  have : Algebra.IsIntegral B' B := Algebra.IsIntegral.tower_top A
  -- the finite morphism `Spec B' ⟶ U`, and the covering of `Spec B'` by the `Spec (Q x).Ring`
  let gU : Spec (.of B') ⟶ c.1.left :=
    Spec.map (CommRingCat.ofHom (algebraMap A B')) ≫ c.1.left.isoSpec.inv
  have : IsFinite gU := by
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B'))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hB')
    infer_instance
  have hQet (x) :
      AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap B' (Q x).Ring))) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale B' (Q x).Ring)))
  let W' (x : s) : (Spec (.of B')).Etale :=
    Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap B' (Q x).Ring)))
  have hW' (p : Spec (.of B')) : ∃ x, ∃ w : (W' x).left, (W' x).hom w = p := by
    obtain ⟨x, r, hr⟩ := PrimeSpectrum.exists_comap_eq_of_isIntegral_of_tensor
      (fun x : s ↦ (P x.1).Ring) (fun x ↦ (Q x).Ring) E (fun p ↦ by
        obtain ⟨x, hx, r, hr⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ p))
        exact ⟨⟨x, hx⟩, r, hr⟩) p
    exact ⟨x, r, hr⟩
  -- a split neighbourhood of `u` for `Spec B' ⟶ U` whose pieces refine the `Spec (Q x).Ring`
  obtain ⟨s₀, hs₀⟩ := SplitNbhd.exists_forall_exists_pieceObj_hom gU c.2.left W' hW'
  choose xt a using hs₀
  -- the neighbourhood `(U', u')` of `y`, and the map `U' ×_Y X ⟶ U' ×_U Spec B'`
  let gm := c.compHom s₀.obj
  let ρ : pullback c.1.hom f ⟶ Spec (.of B') :=
    (pullback c.1.hom f).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B' B))
  have hρ : ρ ≫ gU = pullback.fst c.1.hom f := by
    simp only [ρ, gU, Category.assoc]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    change _ ≫ Spec.map (pullback.fst c.1.hom f).appTop ≫ _ = _
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  let θ : pullback (c.comp s₀.obj).1.hom f ⟶ pullback s₀.obj.1.hom gU :=
    pullback.lift (pullback.fst _ f) ((f.Etale.map gm.val).left ≫ ρ) (by
      rw [Category.assoc, hρ, Hom.etale_map_left_comp_fst]
      rfl)
  refine ⟨c.comp s₀.obj, gm, GeometricFiber gU c.2.left, fun t ↦ θ ⁻¹ᵁ s₀.piece t, ?_,
    ?_, fun t ↦ ?_⟩
  · intro t t' htt'
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, (s₀.disjoint t t' htt').eq_bot,
      Scheme.Hom.preimage_bot]
  · rw [← Scheme.Hom.preimage_iSup, s₀.iSup_eq, Scheme.Hom.preimage_top]
  -- the piece over `t` maps to `Spec (P x).Ring = Spec (B ⊗[B'] (Q x).Ring)`, hence into `R`
  set x := xt t
  set Pc := θ ⁻¹ᵁ s₀.piece t
  let μ₁ : Pc.toScheme ⟶ Spec B :=
    Pc.ι ≫ (f.Etale.map gm.val).left ≫ (pullback c.1.hom f).isoSpec.hom
  let μ₂ : Pc.toScheme ⟶ Spec (.of (Q x).Ring) :=
    θ.resLE (s₀.piece t) Pc le_rfl ≫ (a t).some.left
  have hμ : μ₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B' B)) =
      μ₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap B' (Q x).Ring)) := by
    have h₁ : (a t).some.left ≫ (W' x).hom =
        (s₀.piece t).ι ≫ pullback.snd s₀.obj.1.hom gU :=
      MorphismProperty.Over.w (a t).some
    simp only [μ₁, μ₂, Category.assoc]
    change Pc.ι ≫ (f.Etale.map gm.val).left ≫ ρ =
      θ.resLE _ _ _ ≫ (a t).some.left ≫ (W' x).hom
    rw [h₁, Scheme.Hom.resLE_comp_ι_assoc]
    simp [θ]
  let μ : Pc.toScheme ⟶ Spec (.of (P x.1).Ring) :=
    pullback.lift μ₁ μ₂ hμ ≫ (pullbackSpecIso B' B (Q x).Ring).hom ≫
      Spec.map (CommRingCat.ofHom (E x).symm.toRingEquiv.toRingHom)
  have hμP : μ ≫ Spec.map (CommRingCat.ofHom (algebraMap B (P x.1).Ring)) = μ₁ := by
    have h : CommRingCat.ofHom (algebraMap B (P x.1).Ring) ≫
        CommRingCat.ofHom (E x).symm.toRingEquiv.toRingHom =
          CommRingCat.ofHom (algebraMap B (B ⊗[B'] (Q x).Ring)) := by
      ext b
      exact (E x).symm.commutes b
    simp only [μ, Category.assoc]
    rw [← Spec.map_comp, h, pullbackSpecIso_hom_fst', pullback.lift_fst]
  have hkey : Pc.ι ≫ (f.Etale.map gm.val).left = μ ≫ e x.1 ≫ (g x.1).left := by
    rw [← cancel_mono (pullback c.1.hom f).isoSpec.hom]
    simp only [Category.assoc]
    rw [he, hμP]
  let m : openObj f (c.comp s₀.obj) Pc ⟶ V x.1 :=
    MorphismProperty.Over.homMk (μ ≫ e x.1) (by
      have hg' : (g x.1).left ≫ pullback.snd c.1.hom f = (V x.1).hom :=
        MorphismProperty.Over.w (g x.1)
      change (μ ≫ e x.1) ≫ (V x.1).hom = Pc.ι ≫ pullback.snd _ f
      rw [← hg', Category.assoc, ← Category.assoc (e x.1), ← Category.assoc μ, ← hkey,
        Category.assoc, Hom.etale_map_left_comp_snd])
  have : openIncl f (c.comp s₀.obj) Pc ≫ f.Etale.map gm.val = m ≫ g x.1 :=
    MorphismProperty.Over.Hom.ext hkey
  rw [this]
  exact R.downward_closed (hg x.1) m

/-- **Étale coverings of the base change of an integral morphism are refined by disjoint
decompositions.** Let `(U, u)` be a pointed étale neighbourhood of `y` and `R` a covering sieve
of `U ×_Y X`. Then there is a pointed étale neighbourhood `(U', u') ⟶ (U, u)` and a
decomposition of `U' ×_Y X` into pairwise disjoint opens `P i` whose inclusions, composed with
`U' ×_Y X ⟶ U ×_Y X`, lie in `R`. -/
theorem exists_hom_disjoint_cover (c : Nbhd y) (R : Sieve (f.Etale.obj c.1))
    (hR : R ∈ X.smallEtaleTopology _) :
    ∃ (c' : Nbhd y) (g : c' ⟶ c) (ι : Type u) (P : ι → (pullback c'.1.hom f).Opens),
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧ ⨆ i, P i = ⊤ ∧
        ∀ i, R (openIncl f c' (P i) ≫ f.Etale.map g.val) := by
  obtain ⟨U₁, hU₁, hu, -⟩ := exists_isAffineOpen_mem_and_subset (X := c.1.left)
    (x := c.2.left (default : Spec (.of Ω))) (U := ⊤) trivial
  have : IsAffine (c.restrict U₁ hu).1.left := hU₁
  obtain ⟨c', g, ι, P, hdisj, hsup, hP⟩ := exists_hom_disjoint_cover_of_isAffine f
    (c.restrict U₁ hu) (R.pullback (f.Etale.map (c.restrictHom U₁ hu).val))
    (X.smallEtaleTopology.pullback_stable _ hR)
  refine ⟨c', g ≫ c.restrictHom U₁ hu, ι, P, hdisj, hsup, fun i ↦ ?_⟩
  have := hP i
  rwa [Sieve.pullback_apply, Category.assoc, ← Functor.map_comp,
    Functor.Elements.Hom.val, ← Functor.Elements.comp_hom] at this

end AlgebraicGeometry.Scheme.Hom.Nbhd

end
