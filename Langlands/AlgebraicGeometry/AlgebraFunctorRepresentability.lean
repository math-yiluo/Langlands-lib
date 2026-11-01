/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License 2.0; see licenses/Anthropic-FLT/LICENSE.
Adapted by Worker 344 from
P2M/Sol/S_AlgebraicGeometry_Scheme_exists_represents_of_zariskiSheaf_of_openAffineCover.lean
and its Theorems wrapper at 6e837e75355538c7f80bab5b956861e86c4eacc2.
Changes: focused Library imports, ordinary namespaces, and explicit category
identity equalities/transparency rewrites. See the paired Markdown.
-/
import Langlands.AlgebraicGeometry.AlgebraFunctorSheaf
import Langlands.AlgebraicGeometry.AlgebraFunctorOpenCharts

/-! # Representing an algebra functor by gluing its open affine charts -/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.AlgebraFunctorRepresentability

variable {R : Type} [CommRing R]

section pts

variable (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type) {X : Scheme.{0}}
  (e : G.overTotal.RepresentableBy X)
  (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
  (ev : ∀ (A : Type) [CommRing A] [Algebra R A],
    F A ≃ G.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))))))

abbrev Pts (A : Type) [CommRing A] [Algebra R A] : Type :=
  {g : Spec (CommRingCat.of A) ⟶ X // g ≫ e.overTotalBase = AlgebraFunctorOpenCharts.strMap R A}

variable (A : Type) [CommRing A] [Algebra R A]

noncomputable def toPts (s : F A) : Pts G e A :=
  ⟨e.homEquiv.symm (Functor.OverTotal.ofFibre (Over.mk (AlgebraFunctorOpenCharts.strMap R A)) (ev A s)), by
    have h := e.overTotal_homEquiv_fst
      (e.homEquiv.symm (Functor.OverTotal.ofFibre (Over.mk (AlgebraFunctorOpenCharts.strMap R A)) (ev A s)))
    erw [Equiv.apply_symm_apply, Functor.OverTotal.ofFibre_fst] at h
    exact h.symm⟩

noncomputable def ofPts (g : Pts G e A) : F A :=
  (ev A).symm (Functor.OverTotal.toFibre (Over.mk (AlgebraFunctorOpenCharts.strMap R A)) (e.homEquiv g.1)
    (by rw [e.overTotal_homEquiv_fst]; exact g.2))

lemma ofPts_toPts (s : F A) : ofPts G e F ev A (toPts G e F ev A s) = s := by
  simp only [ofPts, toPts, Equiv.symm_apply_eq]
  exact (Functor.OverTotal.toFibre_congr _ (e.homEquiv.apply_symm_apply _) _ rfl).trans
    (Functor.OverTotal.toFibre_ofFibre _ _)

lemma toPts_ofPts (g : Pts G e A) : toPts G e F ev A (ofPts G e F ev A g) = g := by
  apply Subtype.ext
  simp only [toPts, ofPts, Equiv.apply_symm_apply]
  apply e.homEquiv.injective
  erw [Equiv.apply_symm_apply, Functor.OverTotal.ofFibre_toFibre]

noncomputable def ptEquiv : F A ≃ Pts G e A :=
  ⟨toPts G e F ev A, ofPts G e F ev A, ofPts_toPts G e F ev A, toPts_ofPts G e F ev A⟩

variable {A}

lemma ptEquiv_natural
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (hev : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A)
      (h : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R B))),
      ev B (Fmap A B φ s) =
        G.map (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) h :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))).op (ev A s))
    (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (s : F A) :
    (ptEquiv G e F ev B (Fmap A B φ s)).1 =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ptEquiv G e F ev A s).1 := by
  have h := AlgebraFunctorOpenCharts.spec_comp_strMap (R := R) φ
  change e.homEquiv.symm (Functor.OverTotal.ofFibre (Over.mk (AlgebraFunctorOpenCharts.strMap R B)) (ev B (Fmap A B φ s))) =
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      e.homEquiv.symm (Functor.OverTotal.ofFibre (Over.mk (AlgebraFunctorOpenCharts.strMap R A)) (ev A s))
  erw [hev A B φ s h, e.comp_homEquiv_symm]
  congr 1
  refine Functor.OverTotal.ext' ?_ ?_
  · change AlgebraFunctorOpenCharts.strMap R B = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ AlgebraFunctorOpenCharts.strMap R A
    exact h.symm
  · change G.map _ (G.map _ (G.map _ (ev A s))) = G.map _ (G.map _ (ev A s))
    exact ((Functor.map_op_map_op_apply _ _ _).trans (Functor.map_op_map_op_apply _ _ _)).trans
      ((Functor.map_op_apply_eq_of_left_eq _ _ (by
        change Spec.map (CommRingCat.ofHom φ.toRingHom) =
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ 𝟙 _
        exact (Category.comp_id _).symm) _).trans
        (Functor.map_op_map_op_apply _ _ _).symm)

end pts

lemma P_map
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (Fmap_id : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), Fmap A A (AlgHom.id R A) s = s)
    {ι : Type} (P : ι → ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)
    (isOpen : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A] (s : F A),
      ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
        ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
          P i B (Fmap A B φ s) ↔ Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U)
    (i : ι) {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
    (u : {s : F A // P i A s}) : P i B (Fmap A B φ u.1) := by
  obtain ⟨U, -, hU⟩ := isOpen i A u.1
  have huniv : Set.univ ⊆ U := by
    have h := (hU A (AlgHom.id R A)).mp (by rw [Fmap_id]; exact u.2)
    intro x _
    apply h
    exact ⟨x, PrimeSpectrum.ext (Ideal.comap_id x.asIdeal)⟩
  exact (hU B φ).mpr fun _ _ => huniv trivial

end AlgebraicGeometry.Scheme.AlgebraFunctorRepresentability

open AlgebraicGeometry.Scheme.AlgebraFunctorRepresentability in
theorem AlgebraicGeometry.Scheme.exists_represents_of_zariskiSheaf_of_openAffineCover
    (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (Fmap_id : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), Fmap A A (AlgHom.id R A) s = s)
    (Fmap_comp : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
      [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (s : F A),
      Fmap A C (ψ.comp φ) s = Fmap B C ψ (Fmap A B φ s))
    (sheaf : ∀ (A : Type) [CommRing A] [Algebra R A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra R (B i)]
        [∀ i, IsScalarTower R A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, F (B i)),
      (∀ (i j : Fin n) (C : Type) [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
          [IsLocalization.Away (f i * f j) C] (ρ₁ : B i →ₐ[A] C) (ρ₂ : B j →ₐ[A] C),
          Fmap _ _ (ρ₁.restrictScalars R) (s i) = Fmap _ _ (ρ₂.restrictScalars R) (s j)) →
      ∃! s₀ : F A, ∀ i, Fmap _ _ (IsScalarTower.toAlgHom R A (B i)) s₀ = s i)
    (ι : Type) (P : ι → ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)
    (isOpen : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A] (s : F A),
      ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
        ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
          P i B (Fmap A B φ s) ↔ Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U)
    (S : ι → Type) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (chart : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A], {s : F A // P i A s} ≃ (S i →ₐ[R] A))
    (chart_natural : ∀ (i : ι) (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : {s : F A // P i A s}) (h : P i B (Fmap A B φ s.1)),
      chart i B ⟨Fmap A B φ s.1, h⟩ = φ.comp (chart i A s))
    (cover : ∀ (K : Type) [Field K] [Algebra R K] (s : F K), ∃ i, P i K s) :
    ∃ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        F A ≃ {g : Spec (CommRingCat.of A) ⟶ X // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
      (j : ∀ i, Spec (CommRingCat.of (S i)) ⟶ X),
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A),
          (pt B (Fmap A B φ s)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A s).1) ∧
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ i, j i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (S i)))) ∧
      (∀ y : X, ∃ i, y ∈ Set.range (j i).base) ∧
      (∀ (i : ι) (A : Type) [CommRing A] [Algebra R A] (s : {s : F A // P i A s}),
          (pt A s.1).1 = Spec.map (CommRingCat.ofHom (chart i A s).toRingHom) ≫ j i) := by
  obtain ⟨G, ev, hG, hev⟩ :=
    AlgebraicGeometry.Scheme.exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away R F Fmap
      Fmap_id Fmap_comp sheaf
  obtain ⟨f, hf, hs, hf1⟩ :=
    AlgebraicGeometry.Scheme.exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart R F Fmap Fmap_id
      Fmap_comp G ev hG hev ι P isOpen S chart chart_natural cover
  let Gs : Sheaf Scheme.zariskiTopology (Type) := ⟨G.overTotal, hG⟩
  have hf' : ∀ i, IsOpenImmersion.presheaf
      (show yoneda.obj (Spec (CommRingCat.of (S i))) ⟶ Gs.1 from f i) := hf
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun i => (show yoneda.obj (Spec (CommRingCat.of (S i))) ⟶ Gs.1 from f i))) := hs
  let e : G.overTotal.RepresentableBy _ := Scheme.LocalRepresentability.representableBy (F := Gs) hf'
  let X := (Scheme.LocalRepresentability.glueData (F := Gs) hf').glued
  let j : ∀ i, Spec (CommRingCat.of (S i)) ⟶ X := fun i =>
    Scheme.LocalRepresentability.toGlued (F := Gs) hf' i

  let u : ∀ i, {s : F (S i) // P i (S i) s} := fun i => (chart i (S i)).symm (AlgHom.id R (S i))
  have hej : ∀ i, e.homEquiv (j i) = ⟨AlgebraFunctorOpenCharts.strMap R (S i), ev (S i) (u i).1⟩ := fun i => by
    have h1 : e.homEquiv (j i) = yonedaEquiv (f i) :=
      Scheme.LocalRepresentability.yonedaGluedToSheaf_app_toGlued (F := Gs) hf'
    rw [h1, yonedaEquiv_apply]
    exact hf1 i
  have hjp : ∀ i, j i ≫ e.overTotalBase = AlgebraFunctorOpenCharts.strMap R (S i) := fun i => by
    rw [← e.overTotal_homEquiv_fst, hej]
  have hju : ∀ i, (ptEquiv G e F ev (S i) (u i).1).1 = j i := fun i => by
    change e.homEquiv.symm (Functor.OverTotal.ofFibre (Over.mk (AlgebraFunctorOpenCharts.strMap R (S i))) (ev (S i) (u i).1)) = j i
    refine (Equiv.symm_apply_eq _).mpr (Eq.trans ?_ (hej i).symm)
    refine Functor.OverTotal.ext' rfl ?_
    change G.map _ (G.map _ (ev (S i) (u i).1)) = ev (S i) (u i).1
    exact Functor.map_op_map_op_apply_eq_self _ _ (by simp) _
  refine ⟨X, e.overTotalBase, fun A _ _ => ptEquiv G e F ev A, j,
    fun A B _ _ _ _ φ s => ptEquiv_natural G e F ev Fmap hev B φ s,
    fun i => inferInstance, hjp, fun y => ?_, fun i A _ _ s => ?_⟩
  · obtain ⟨i, z, hz⟩ := (Scheme.LocalRepresentability.glueData (F := Gs) hf').ι_jointly_surjective y
    exact ⟨i, z, hz⟩
  · have hPu : P i A (Fmap (S i) A (chart i A s) (u i).1) := P_map F Fmap Fmap_id P isOpen i _ (u i)
    have hs' : s = ⟨Fmap (S i) A (chart i A s) (u i).1, hPu⟩ := by
      apply (chart i A).injective
      rw [chart_natural i (S i) A (chart i A s) (u i) hPu]
      change chart i A s = (chart i A s).comp (chart i (S i) ((chart i (S i)).symm (AlgHom.id R (S i))))
      rw [Equiv.apply_symm_apply, AlgHom.comp_id]
    conv_lhs => rw [hs']
    rw [ptEquiv_natural G e F ev Fmap hev A (chart i A s) (u i).1, hju]
