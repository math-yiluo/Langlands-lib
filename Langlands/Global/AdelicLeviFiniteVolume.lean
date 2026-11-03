import Langlands.Global.LeftCosetSemidirectFiniteVolume
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Finite volume through a split kernel with compact rational quotient

Let `p : G ⟶ L` be a homomorphism of affine finite-type group schemes over a number field
`F` with a homomorphic section `j : L ⟶ G`, and let `U` be the scheme-theoretic kernel of
`p`. If `U(F) \ U(𝔸)` is compact and `L(F) \ L(𝔸)¹` has finite Haar volume, then
`G(F) \ G(𝔸)¹` has finite Haar volume. This is the Levi reduction step towards finite
volume (Getz–Hahn, Theorem 2.6.3), to be applied with `L` a Levi factor and `U` the
unipotent radical.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry NumberField MeasureTheory Set Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}

/-- Postcomposition with a morphism that is surjective on global sections is a topological
embedding of coefficient points. -/
theorem isEmbedding_affinePointPostcomp [IsAffine G.X.left] (f : G.X ⟶ H.X)
    (hf : Function.Surjective f.left.appTop) (A : CommAlgCat.{u} R) [TopologicalSpace A] :
    IsEmbedding (fun x : G.affinePoints A => x ≫ f) := by
  let φ : (Γ(G.X.left, ⊤) → A) → (Γ(H.X.left, ⊤) → A) := fun g a => g (f.left.appTop a)
  have hφ : IsEmbedding φ := by
    refine Function.LeftInverse.isEmbedding
      (f := fun g b => g (Function.surjInv hf b)) (fun g => ?_) ?_ ?_
    · funext b
      simp only [φ, Function.surjInv_eq hf b]
    · exact continuous_pi fun b => continuous_apply _
    · exact continuous_pi fun a => continuous_apply _
  have hcomp : IsEmbedding ((fun y : H.affinePoints A => (H.affinePointEvaluation A y : _ → A)) ∘
      (fun x : G.affinePoints A => x ≫ f)) :=
    hφ.comp (G.isEmbedding_affinePointEvaluation A)
  have hH : IsInducing (fun y : H.affinePoints A => (H.affinePointEvaluation A y : _ → A)) :=
    ⟨rfl⟩
  exact ⟨hH.of_comp_iff.mp hcomp.isInducing, hcomp.injective.of_comp⟩

end Langlands.GroupScheme

namespace Langlands.Global

namespace LeftCosetSpace

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A compact left quotient of a locally compact group is covered by the image of one compact
set: every point has a left `Γ`-translate in it. -/
theorem exists_isCompact_cover [LocallyCompactSpace H] (Γ : Subgroup H)
    [CompactSpace (LeftCosetSpace Γ)] :
    ∃ K : Set H, IsCompact K ∧ ∀ h : H, ∃ γ ∈ Γ, γ * h ∈ K := by
  choose K hK hKx using fun x : H => exists_compact_mem_nhds x
  have hopen : ∀ x, IsOpen (mk Γ '' interior (K x)) := fun x =>
    (isOpenQuotientMap_mk Γ).isOpenMap _ isOpen_interior
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => mk Γ '' interior (K x)) hopen
    (fun q _ => by
      obtain ⟨x, rfl⟩ := mk_surjective Γ q
      exact mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hKx x), rfl⟩)
  refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hK x, fun h => ?_⟩
  obtain ⟨x, hx, y, hy, hyh⟩ := mem_iUnion₂.mp (ht (mem_univ (mk Γ h)))
  have hγ : h * y⁻¹ ∈ Γ := (mk_eq_mk_iff Γ y h).mp hyh
  refine ⟨y * h⁻¹, ?_, ?_⟩
  · simpa only [mul_inv_rev, inv_inv] using Γ.inv_mem hγ
  · rw [inv_mul_cancel_right]
    exact mem_biUnion hx (interior_subset hy)

end LeftCosetSpace

namespace AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]

section Embedding

variable {U G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]

/-- A homomorphism surjective on global sections embeds adelic points. -/
theorem isEmbedding_map_of_surjective (f : U ⟶ G)
    (hf : Function.Surjective f.hom.hom.left.appTop) : IsEmbedding (map F U G f) :=
  GroupScheme.isEmbedding_affinePointPostcomp f.hom.hom hf _

/-- A homomorphism surjective on global sections embeds norm-one adelic points. -/
theorem isEmbedding_mapNormOne_of_surjective (f : U ⟶ G)
    (hf : Function.Surjective f.hom.hom.left.appTop) : IsEmbedding (mapNormOne F U G f) := by
  have h : IsEmbedding ((Subtype.val : normOneSubgroup F G → AdelicGroupPoints F G) ∘
      mapNormOne F U G f) :=
    (isEmbedding_map_of_surjective F f hf).comp IsEmbedding.subtypeVal
  exact IsEmbedding.subtypeVal.of_comp_iff.mp h

end Embedding

section Compact

variable (U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine U.X.left]
  [LocallyOfFiniteType U.X.hom]

/-- If `U(F) \ U(𝔸)` is compact, every adelic point of `U` has norm one: each character norm
has compact image, a compact subgroup of `ℝ≥0ˣ`. -/
theorem mem_normOneSubgroup_of_compactSpace [CompactSpace (RationalQuotient F U)]
    (x : AdelicGroupPoints F U) : x ∈ normOneSubgroup F U := by
  obtain ⟨K, hK, hcover⟩ := LeftCosetSpace.exists_isCompact_cover (rationalSubgroup F U)
  refine (mem_normOneSubgroup F U x).mpr fun χ => ?_
  set φ := characterNorm F U χ
  have hrange : (φ.toMonoidHom.range : Set ℝ≥0ˣ) = φ '' K := by
    apply Subset.antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨γ, ⟨z, rfl⟩, hγ⟩ := hcover y
      refine ⟨_, hγ, ?_⟩
      simp [φ, map_mul]
    · rintro _ ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
  have hc : IsCompact (φ.toMonoidHom.range : Set ℝ≥0ˣ) := hrange ▸ hK.image φ.continuous
  exact continuousMonoidHom_eq_one_on_compactSubgroup (ContinuousMonoidHom.id ℝ≥0ˣ) _ hc
    ⟨x, rfl⟩

end Compact

section Levi

variable {G L : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom]

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [LocallyOfFiniteType L.X.hom] in
/-- The kernel inclusion of a homomorphism into an affine group scheme is a closed
immersion. -/
theorem kernel_isClosedImmersion (p : G ⟶ L) :
    IsClosedImmersion (GroupScheme.kernelι p).hom.hom.left := by
  have : IsSeparated L.X.hom := IsSeparated.of_isAffineHom L.X.hom
  infer_instance

omit [NumberField F] [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType L.X.hom] in
/-- The kernel of a homomorphism of affine group schemes is affine. -/
theorem kernel_isAffine (p : G ⟶ L) : IsAffine (GroupScheme.kernel p).X.left :=
  have := kernel_isClosedImmersion F p
  (IsClosedImmersion.isAffine_surjective_of_isAffine (GroupScheme.kernelι p).hom.hom.left).1

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType L.X.hom] in
/-- The kernel of a homomorphism of finite-type affine group schemes is of finite type. -/
theorem kernel_locallyOfFiniteType (p : G ⟶ L) :
    LocallyOfFiniteType (GroupScheme.kernel p).X.hom := by
  have := kernel_isClosedImmersion F p
  rw [← (GroupScheme.kernelι p).hom.hom.w]
  infer_instance

/-- **Levi reduction for finite volume.** Let `p : G ⟶ L` have a homomorphic section `j`.
If the kernel of `p` has compact rational adelic quotient and `L(F) \ L(𝔸)¹` has finite Haar
volume, then `G(F) \ G(𝔸)¹` has finite Haar volume. -/
theorem isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_section
    (p : G ⟶ L) (j : L ⟶ G) (hjp : j ≫ p = 𝟙 L)
    [CompactSpace (RationalQuotient F (GroupScheme.kernel p))]
    [IsFiniteMeasure (normOneRationalQuotientHaarMeasure F L)] :
    IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G) := by
  have := kernel_isAffine F p
  have := kernel_locallyOfFiniteType F p
  have := kernel_isClosedImmersion F p
  set U := GroupScheme.kernel p
  set e := GroupScheme.kernelι p
  let T := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (AdeleRing (𝓞 F) F)))
  let i := mapNormOne F U G e
  let jN := mapNormOne F L G j
  let pN := mapNormOne F G L p
  have hjp' : j.hom.hom ≫ p.hom.hom = 𝟙 L.X := by
    simpa using congrArg (fun f => f.hom.hom) hjp
  have hpj : ∀ m, pN (jN m) = m := fun m => by
    apply Subtype.ext
    change ((m : AdelicGroupPoints F L) ≫ j.hom.hom) ≫ p.hom.hom = m
    rw [Category.assoc, hjp', Category.comp_id]
  have hpi : ∀ n, pN (i n) = 1 := fun n => by
    apply Subtype.ext
    exact (GroupScheme.kernelPointsEquiv p T (n : AdelicGroupPoints F U)).property
  have hker : ∀ h, pN h = 1 → ∃ n, i n = h := fun h hh => by
    have hh' : (h : AdelicGroupPoints F G) ≫ p.hom.hom = 1 := congrArg Subtype.val hh
    let y := (GroupScheme.kernelPointsEquiv p T).symm ⟨h.1, hh'⟩
    refine ⟨⟨y, mem_normOneSubgroup_of_compactSpace F U y⟩, ?_⟩
    apply Subtype.ext
    change y ≫ e.hom.hom = h.1
    exact congrArg Subtype.val ((GroupScheme.kernelPointsEquiv p T).apply_symm_apply ⟨h.1, hh'⟩)
  have hi : IsEmbedding i := isEmbedding_mapNormOne_of_surjective F e
    (IsClosedImmersion.isAffine_surjective_of_isAffine e.hom.hom.left).2
  obtain ⟨K0, hK0, hcover⟩ := LeftCosetSpace.exists_isCompact_cover (rationalSubgroup F U)
  have hK : IsCompact (Subtype.val ⁻¹' K0 : Set (normOneSubgroup F U)) :=
    (isClosed_normOneSubgroup F U).isClosedEmbedding_subtypeVal.isCompact_preimage hK0
  have hKcover : ∀ n : normOneSubgroup F U, ∃ γ, i γ ∈ rationalNormOneSubgroup F G ∧
      γ * n ∈ (Subtype.val ⁻¹' K0 : Set (normOneSubgroup F U)) := fun n => by
    obtain ⟨_, ⟨z, rfl⟩, hγ⟩ := hcover n
    refine ⟨rationalNormOne F U z, ?_, hγ⟩
    rw [mapNormOne_rationalNormOne]
    exact ⟨_, rfl⟩
  have hjΓ : ∀ γ ∈ rationalNormOneSubgroup F L, jN γ ∈ rationalNormOneSubgroup F G := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, (mapNormOne_rationalNormOne F L G j x).symm⟩
  have : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure (rationalNormOneSubgroup F L)
      (isDiscrete_rationalNormOneSubgroup F L)) :=
    ‹IsFiniteMeasure (normOneRationalQuotientHaarMeasure F L)›
  exact LeftCosetSpace.Semidirect.isFiniteMeasure_haarQuotientMeasure
    (i := i.toMonoidHom) (j := jN.toMonoidHom) (p := pN.toMonoidHom) hpj hker hpi hi
    jN.continuous pN.continuous (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G) hK hKcover (rationalNormOneSubgroup F L)
    (isDiscrete_rationalNormOneSubgroup F L) hjΓ

end Levi

/-- **Levi reduction for finite volume**, over every number field `F`: for affine finite-type
group schemes `G` and `L` over `F` and homomorphisms `p : G ⟶ L`, `j : L ⟶ G` with
`j ≫ p = 𝟙 L`, if the rational adelic quotient of the kernel of `p` is compact and
`L(F) \ L(𝔸)¹` has finite Haar volume, then `G(F) \ G(𝔸)¹` has finite Haar volume. -/
def LeviReductionFiniteVolumeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G L : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom]
    (p : G ⟶ L) (j : L ⟶ G), j ≫ p = 𝟙 L →
      CompactSpace (RationalQuotient F (GroupScheme.kernel p)) →
      IsFiniteMeasure (normOneRationalQuotientHaarMeasure F L) →
      IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G)

theorem leviReductionFiniteVolumeStatement : LeviReductionFiniteVolumeStatement.{u} :=
  fun F _ _ _ _ _ _ _ _ p j hjp _ _ =>
    isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_section F p j hjp

end AdelicGroupPoints

end Langlands.Global
