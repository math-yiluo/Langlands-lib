import Langlands.GroupScheme.Dynamic.BaseChangeCoordinates

/-! # Spectra of algebras over a field, and field points in opens of an affine scheme

For a field `k`, `algOver k A` is `Spec A` as a scheme over `Spec k`, and `algOverHom φ` is the
morphism given by a `k`-algebra map `φ`. Every nonempty open of `Spec R` contains the field
points `Spec L → Spec R` of all ring maps `φ` with `φ f ≠ 0`, for some nonzero `f ∈ R`.
`evalMap L a : L ⊗[k] B → L` evaluates at a `k`-point `a`. Field points of the target of a
surjective morphism lift over a field extension.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Corepresented

variable {k : Type u} [Field k]

section AlgOver

variable (A : Type u) [CommRing A] [Algebra k A]

variable (k) in
/-- `Spec A` as a scheme over `Spec k`. -/
abbrev algOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

variable {A} {A' A'' : Type u} [CommRing A'] [Algebra k A'] [CommRing A''] [Algebra k A'']

theorem specMap_comp_specMap_algebraMap (φ : A →ₐ[k] A') :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k A')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext φ.commutes

/-- The morphism `Spec A' ⟶ Spec A` over `Spec k` given by a `k`-algebra map `A → A'`. -/
def algOverHom (φ : A →ₐ[k] A') : algOver k A' ⟶ algOver k A :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specMap_comp_specMap_algebraMap φ)

theorem algOverHom_comp (φ : A →ₐ[k] A') (φ' : A' →ₐ[k] A'') :
    algOverHom φ' ≫ algOverHom φ = algOverHom (φ'.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem algOverHom_id : algOverHom (AlgHom.id k A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  rfl

/-- Every morphism `Spec A' ⟶ Spec A` over `Spec k` comes from a `k`-algebra map. -/
theorem exists_eq_algOverHom (b : algOver k A' ⟶ algOver k A) : ∃ φ : A →ₐ[k] A', b = algOverHom φ := by
  have hc : CommRingCat.ofHom (algebraMap k A) ≫ Spec.preimage b.left =
      CommRingCat.ofHom (algebraMap k A') := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact Over.w b
  refine ⟨⟨(Spec.preimage b.left).hom, fun r => congrArg (fun ψ => ψ.hom r) hc⟩, ?_⟩
  apply Over.OverMorphism.ext
  change b.left = Spec.map (CommRingCat.ofHom (Spec.preimage b.left).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

variable {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}

theorem algOverHom_comp_ofAlgHom (φ : A →ₐ[k] A') (ψ : B →ₐ[k] A) :
    algOverHom φ ≫ ofAlgHom F e ψ = ofAlgHom F e (φ.comp ψ) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom ψ.toRingHom) (CommRingCat.ofHom φ.toRingHom)).symm

end AlgOver

section BasicOpen

/-- Every nonempty open `O` of `Spec R` contains the image of `Spec L → Spec R` for every ring
map `φ : R → L` to a field with `φ f ≠ 0`, for some nonzero `f ∈ R`. -/
theorem exists_ne_zero_range_subset {R : Type u} [CommRing R] (O : Set (Spec (CommRingCat.of R)))
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ f : R, f ≠ 0 ∧ ∀ (L : Type u) [Field L] (φ : R →+* L), φ f ≠ 0 →
      Set.range (Spec.map (CommRingCat.ofHom φ)) ⊆ O := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hO
  refine ⟨f, ?_, fun L _ φ hφ => ?_⟩
  · rintro rfl
    exact hxf (Ideal.zero_mem _)
  · rintro _ ⟨t, rfl⟩
    apply hfO
    rw [Spec.map_apply]
    change f ∉ Ideal.comap _ _
    rw [Ideal.mem_comap]
    have := t.isPrime
    have : t.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [this, Ideal.mem_bot]
    exact hφ

variable {B : Type u} [CommRing B] [Algebra k B] (L : Type u) [Field L] [Algebra k L]

/-- The evaluation `L ⊗[k] B → L` at a `k`-point `a`. -/
def evalMap (a : B →ₐ[k] k) : L ⊗[k] B →ₐ[k] L :=
  Algebra.TensorProduct.lift (AlgHom.id k L) ((Algebra.ofId k L).comp a) fun _ _ =>
    Commute.all _ _

theorem evalMap_tmul (a : B →ₐ[k] k) (l : L) (b : B) :
    evalMap L a (l ⊗ₜ b) = l * algebraMap k L (a b) := by
  rw [evalMap, Algebra.TensorProduct.lift_tmul]
  rfl

/-- The evaluation is `L ⊗ a` followed by `L ⊗[k] k ≅ L`. -/
theorem evalMap_apply (a : B →ₐ[k] k) (f : L ⊗[k] B) :
    evalMap L a f = TensorProduct.rid k L (Algebra.TensorProduct.map (AlgHom.id k L) a f) := by
  induction f with
  | tmul l b =>
    rw [evalMap_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.rid_tmul, AlgHom.id_apply,
      Algebra.smul_def, mul_comm]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end BasicOpen

section Lift

/-- A field point of the target of a surjective morphism lifts over some field extension: for
`x : Spec L ⟶ Q` with `L` a nonzero ring and `q : Y ⟶ Q` with surjective underlying map, there
are a field `K'`, a `k`-algebra map `β : L → K'` and a point `y : Spec K' ⟶ Y` with
`x ∘ Spec β = q ∘ y`. -/
theorem exists_lift_of_surjective {L : Type u} [CommRing L] [Nontrivial L] [Algebra k L]
    {Y Q : Over (Spec (CommRingCat.of k))} (q : Y ⟶ Q) [Surjective q.left]
    (x : algOver k L ⟶ Q) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra k K') (β : L →ₐ[k] K') (y : algOver k K' ⟶ Y),
      algOverHom β ≫ x = y ≫ q := by
  obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  obtain ⟨v, -⟩ : t ∈ Set.range (pullback.fst x.left q.left) := by
    rw [Scheme.Pullback.range_fst, (Set.range_eq_univ (f := q.left)).2 q.left.surjective]
    trivial
  let s := (pullback x.left q.left).fromSpecResidueField v
  let K' := (pullback x.left q.left).residueField v
  let sL := s ≫ pullback.fst x.left q.left
  let ρ : CommRingCat.of k ⟶ K' := Spec.preimage (sL ≫ (algOver k L).hom)
  let _ : Algebra k K' := ρ.hom.toAlgebra
  let β : L →ₐ[k] K' :=
    { (Spec.preimage (R := CommRingCat.of L) sL).hom with
      commutes' := fun r => by
        have h : CommRingCat.ofHom (algebraMap k L) ≫ Spec.preimage (R := CommRingCat.of L) sL =
            ρ := by
          apply Spec.map_injective
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
          rfl
        exact congrArg (fun φ => φ.hom r) h }
  let y : algOver k K' ⟶ Y := Over.homMk (s ≫ pullback.snd x.left q.left) (by
    change (s ≫ pullback.snd x.left q.left) ≫ Y.hom = Spec.map (CommRingCat.ofHom ρ.hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, Category.assoc, ← Over.w q,
      ← pullback.condition_assoc, Over.w x])
  refine ⟨K', inferInstance, inferInstance, β, y, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (Spec.preimage (R := CommRingCat.of L) sL).hom) ≫ x.left =
    (s ≫ pullback.snd x.left q.left) ≫ q.left
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  simp only [sL, Category.assoc, pullback.condition]

end Lift

end Corepresented

end Langlands.GroupScheme
