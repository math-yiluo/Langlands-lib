import Langlands.Cohomology.Tate.Coinduced

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

/-- The coinduced replacement, as a coefficient functor. -/
def coinducedFunctor : Rep.{u} R G ⥤ Rep.{u} R G :=
  Rep.resFunctor (⊥ : Subgroup G).subtype ⋙ Rep.coindFunctor R (⊥ : Subgroup G).subtype

lemma coinducedFunctor_map_apply {A B : Rep.{u} R G} (f : A ⟶ B)
    (v : coinduced A) (g : G) :
    ((coinducedFunctor.map f).hom v).1 g = f.hom (v.1 g) := rfl

lemma coinducedEmbedding_naturality {A B : Rep.{u} R G} (f : A ⟶ B) :
    coinducedEmbedding A ≫ coinducedFunctor.map f = f ≫ coinducedEmbedding B := by
  ext a
  apply Subtype.ext
  funext g
  exact Rep.hom_comm_apply f g a

instance coinducedEmbedding_mono (A : Rep.{u} R G) : Mono (coinducedEmbedding A) :=
  (Rep.mono_iff_injective _).mpr fun a b h => by
    exact (coinducedEvaluation_embedding A a).symm.trans
      ((congrArg (coinducedEvaluation A) h).trans (coinducedEvaluation_embedding A b))

/-- The positive coefficient shift is the actual cokernel of the coinduced embedding. -/
abbrev shiftUp (A : Rep.{u} R G) : Rep.{u} R G := cokernel (coinducedEmbedding A)

/-- The canonical exact sequence used to lower a cohomological degree by one. -/
abbrev shiftUpSequence (A : Rep.{u} R G) : ShortComplex (Rep.{u} R G) :=
  ShortComplex.mk (coinducedEmbedding A) (cokernel.π (coinducedEmbedding A))
    (cokernel.condition _)

lemma shiftUpSequence_shortExact (A : Rep.{u} R G) :
    (shiftUpSequence A).ShortExact where
  exact := ShortComplex.exact_cokernel _

/-- The map of coefficient cokernels induced by an equivariant coefficient map. -/
def shiftUpMap {A B : Rep.{u} R G} (f : A ⟶ B) : shiftUp A ⟶ shiftUp B :=
  cokernel.map (coinducedEmbedding A) (coinducedEmbedding B) f (coinducedFunctor.map f)
    (coinducedEmbedding_naturality f)

/-- The positive coefficient shift is functorial. -/
def shiftUpFunctor : Rep.{u} R G ⥤ Rep.{u} R G where
  obj := shiftUp
  map := shiftUpMap
  map_id A := by
    apply (cancel_epi (cokernel.π (coinducedEmbedding A))).mp
    simp only [shiftUpMap, cokernel.π_desc, Category.comp_id]
    exact Category.id_comp _
  map_comp f g := by
    apply (cancel_epi (cokernel.π (coinducedEmbedding _))).mp
    simp [shiftUpMap, Category.assoc]

/-- The map of embedding sequences determined by a coefficient morphism. -/
def shiftUpSequenceMap {A B : Rep.{u} R G} (f : A ⟶ B) :
    shiftUpSequence A ⟶ shiftUpSequence B where
  τ₁ := f
  τ₂ := coinducedFunctor.map f
  τ₃ := shiftUpMap f
  comm₁₂ := (coinducedEmbedding_naturality f).symm
  comm₂₃ := by simp [shiftUpMap]

/-- The embedding sequence splits after forgetting the group action. -/
def shiftUpSequence_scalarSplitting (A : Rep.{u} R G) :
    ((shiftUpSequence A).map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting := by
  let hS := (shiftUpSequence_shortExact A).map_of_exact
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
  exact ShortComplex.Splitting.ofExactOfRetraction _ hS.exact
    (ModuleCat.ofHom (coinducedEvaluation A))
    (by ext a; exact coinducedEvaluation_embedding A a) hS.epi_g

variable [Fintype G]

/-- The equivariant augmentation from functions, with the right-translation convention. -/
def coinducedProjectionLinear (A : Rep.{u} R G) : coinduced A →ₗ[R] A :=
  ∑ g : G, (A.ρ g⁻¹).comp
    ((LinearMap.proj g).comp (coinducedFunctions A).symm.toLinearMap)

lemma coinducedProjectionLinear_apply (A : Rep.{u} R G) (f : coinduced A) :
    coinducedProjectionLinear A f = ∑ g : G, A.ρ g⁻¹ (f.1 g) := by
  simp [coinducedProjectionLinear, coinducedFunctions]

lemma coinducedProjectionLinear_equivariant (A : Rep.{u} R G) (g : G)
    (f : coinduced A) :
    coinducedProjectionLinear A ((coinduced A).ρ g f) =
      A.ρ g (coinducedProjectionLinear A f) := by
  rw [coinducedProjectionLinear_apply, coinducedProjectionLinear_apply]
  change (∑ x : G, A.ρ x⁻¹ (f.1 (x * g))) = A.ρ g (∑ x : G, A.ρ x⁻¹ (f.1 x))
  calc
    (∑ x : G, A.ρ x⁻¹ (f.1 (x * g))) =
        ∑ x : G, A.ρ g (A.ρ (x * g)⁻¹ (f.1 (x * g))) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [← Module.End.mul_apply, ← map_mul, mul_inv_rev]
    _ = ∑ x : G, A.ρ g (A.ρ x⁻¹ (f.1 x)) :=
      Equiv.sum_comp (Equiv.mulRight g) (fun x => A.ρ g (A.ρ x⁻¹ (f.1 x)))
    _ = A.ρ g (∑ x : G, A.ρ x⁻¹ (f.1 x)) := (map_sum _ _ _).symm

/-- The coinduced augmentation is an actual morphism of representations. -/
def coinducedProjection (A : Rep.{u} R G) : coinduced A ⟶ A :=
  Rep.ofHom ⟨coinducedProjectionLinear A, fun g => by
    ext f
    exact coinducedProjectionLinear_equivariant A g f⟩

lemma coinducedProjection_naturality {A B : Rep.{u} R G} (f : A ⟶ B) :
    coinducedProjection A ≫ f = coinducedFunctor.map f ≫ coinducedProjection B := by
  ext v
  change f.hom (coinducedProjectionLinear A v) =
    coinducedProjectionLinear B ((coinducedFunctor.map f).hom v)
  rw [coinducedProjectionLinear_apply, coinducedProjectionLinear_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact Rep.hom_comm_apply f g⁻¹ (v.1 g)

lemma coinducedProjection_delta (A : Rep.{u} R G) (a : A) :
    (coinducedProjection A).hom (coinducedDelta A a) = a := by
  classical
  change coinducedProjectionLinear A (coinducedDelta A a) = a
  rw [coinducedProjectionLinear_apply]
  calc
    (∑ g : G, A.ρ g⁻¹ ((coinducedDelta A a).1 g)) =
        ∑ g : G, A.ρ g⁻¹ (if g = 1 then a else 0) :=
      Finset.sum_congr rfl (fun g _ =>
        congrArg (A.ρ g⁻¹) (coinducedDelta_apply A a g))
    _ = a := by simp only [apply_ite, map_zero]; simp

instance coinducedProjection_epi (A : Rep.{u} R G) : Epi (coinducedProjection A) :=
  (Rep.epi_iff_surjective _).mpr fun a => ⟨coinducedDelta A a, coinducedProjection_delta A a⟩

/-- The negative coefficient shift is the actual kernel of the coinduced augmentation. -/
abbrev shiftDown (A : Rep.{u} R G) : Rep.{u} R G := kernel (coinducedProjection A)

/-- The canonical exact sequence used to raise a cohomological degree by one. -/
abbrev shiftDownSequence (A : Rep.{u} R G) : ShortComplex (Rep.{u} R G) :=
  ShortComplex.mk (kernel.ι (coinducedProjection A)) (coinducedProjection A)
    (kernel.condition _)

lemma shiftDownSequence_shortExact (A : Rep.{u} R G) :
    (shiftDownSequence A).ShortExact where
  exact := ShortComplex.exact_kernel _

/-- The map of coefficient kernels induced by an equivariant coefficient map. -/
def shiftDownMap {A B : Rep.{u} R G} (f : A ⟶ B) : shiftDown A ⟶ shiftDown B :=
  kernel.map (coinducedProjection A) (coinducedProjection B) (coinducedFunctor.map f) f
    (coinducedProjection_naturality f)

/-- The negative coefficient shift is functorial. -/
def shiftDownFunctor : Rep.{u} R G ⥤ Rep.{u} R G where
  obj := shiftDown
  map := shiftDownMap
  map_id A := by
    apply (cancel_mono (kernel.ι (coinducedProjection A))).mp
    simp only [shiftDownMap, kernel.lift_ι, Category.id_comp]
    exact Category.comp_id _
  map_comp f g := by
    apply (cancel_mono (kernel.ι (coinducedProjection _))).mp
    simp [shiftDownMap, Category.assoc]

/-- The map of augmentation sequences determined by a coefficient morphism. -/
def shiftDownSequenceMap {A B : Rep.{u} R G} (f : A ⟶ B) :
    shiftDownSequence A ⟶ shiftDownSequence B where
  τ₁ := shiftDownMap f
  τ₂ := coinducedFunctor.map f
  τ₃ := f
  comm₁₂ := by simp [shiftDownMap]
  comm₂₃ := (coinducedProjection_naturality f).symm

/-- The augmentation sequence splits after forgetting the group action. -/
def shiftDownSequence_scalarSplitting (A : Rep.{u} R G) :
    ((shiftDownSequence A).map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting := by
  let hS := (shiftDownSequence_shortExact A).map_of_exact
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
  exact ShortComplex.Splitting.ofExactOfSection _ hS.exact
    (ModuleCat.ofHom (coinducedDelta A))
    (by ext a; exact coinducedProjection_delta A a) hS.mono_f

/-- The actual Tate connecting map is invertible when both adjacent middle terms vanish. -/
lemma tate_delta_isIso {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact) (n : ℤ)
    (h₀ : IsZero (tateCohomology S.X₂ n))
    (h₁ : IsZero (tateCohomology S.X₂ (n + 1))) :
    IsIso (TateCohomology.δ hS n) := by
  have hm : Mono (TateCohomology.δ hS n) :=
    (TateCohomology.exact₃ hS n).mono_g (h₀.eq_of_src _ _)
  have he : Epi (TateCohomology.δ hS n) :=
    (TateCohomology.exact₁ hS n).epi_f (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Dimension shifting down in degree, using a proved acyclic middle representation. -/
def shiftUpIso (A : Rep.{u} R G) (n : ℤ) :
    tateCohomology (shiftUp A) n ≅ tateCohomology A (n + 1) := by
  have := tate_delta_isIso (shiftUpSequence_shortExact A) n
    (coinduced_tate_isZero A n) (coinduced_tate_isZero A (n + 1))
  exact asIso (TateCohomology.δ (shiftUpSequence_shortExact A) n)

/-- Dimension shifting up in degree, using a proved acyclic middle representation. -/
def shiftDownIso (A : Rep.{u} R G) (n : ℤ) :
    tateCohomology A n ≅ tateCohomology (shiftDown A) (n + 1) := by
  have := tate_delta_isIso (shiftDownSequence_shortExact A) n
    (coinduced_tate_isZero A n) (coinduced_tate_isZero A (n + 1))
  exact asIso (TateCohomology.δ (shiftDownSequence_shortExact A) n)

lemma shiftUpIso_naturality {A B : Rep.{u} R G} (f : A ⟶ B) (n : ℤ) :
    (shiftUpIso A n).hom ≫ (tateCohomologyFunctor (n + 1)).map f =
      (tateCohomologyFunctor n).map (shiftUpMap f) ≫ (shiftUpIso B n).hom :=
  TateCohomology.δ_naturality (shiftUpSequence_shortExact A)
    (shiftUpSequence_shortExact B) (shiftUpSequenceMap f) n

lemma shiftDownIso_naturality {A B : Rep.{u} R G} (f : A ⟶ B) (n : ℤ) :
    (shiftDownIso A n).hom ≫ (tateCohomologyFunctor (n + 1)).map (shiftDownMap f) =
      (tateCohomologyFunctor n).map f ≫ (shiftDownIso B n).hom :=
  TateCohomology.δ_naturality (shiftDownSequence_shortExact A)
    (shiftDownSequence_shortExact B) (shiftDownSequenceMap f) n

end Langlands.Tate
