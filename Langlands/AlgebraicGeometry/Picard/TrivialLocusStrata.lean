import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeSections
import Langlands.LinearAlgebra.KernelColumnSplit
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof

/-! # Field points of the triviality locus and column splits

Every point in the image of a member of the fppf triviality locus of a line bundle comes from a
field point along which the bundle is trivial. At such a point the matrix of a two-term complex
computing sections has a column split with the expected number of remaining columns, and
members of the triviality locus where its scalar is invertible factor through the stratum on
which its Schur complement vanishes.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open Scheme.TwoAffineOpenCover (moduleSectionsOfHom specMap)
open Langlands.AlgebraicGeometry.AlgebraicSpace (specOver)

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativePicard

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

/-- A family of `A`-linear identifications of the global sections of the base changes of `N`
with the kernels of a two-term complex `G`, as produced by the FLT port's theorem
`exists_twoTermComplex_sectionsEquiv_forall_baseChange`. -/
abbrev SectionsEquivs {R : Type u} [CommRing R] [Algebra k R]
    (N : LineBundle ((relativeSpace X.hom).obj (specOver k R)))
    (G : CoherentBaseChange.TwoTermComplex.{u, u} R) : Type (u + 1) :=
  ∀ (A : Type u) [CommRing A] [Algebra R A],
    letI := moduleSectionsOfHom (pullback.snd (baseMap X R) (specMap R A))
      ((Scheme.Modules.pullback (pullback.fst (baseMap X R) (specMap R A))).obj N.obj) ⊤
    Γ((Scheme.Modules.pullback (pullback.fst (baseMap X R) (specMap R A))).obj N.obj, ⊤) ≃ₗ[A]
      G.H0 A

set_option backward.isDefEq.respectTransparency.types false in
/-- Every point in the image of a member of the triviality locus is the image of a field point
along which the bundle is trivial. -/
theorem exists_field_of_mem_trivialLocus {R : Type u} [CommRing R] [Algebra k R]
    {N : LineBundle ((relativeSpace X.hom).obj (specOver k R))} {T' : Scheme.{u}}
    {g : T' ⟶ Spec (.of R)} (hg : trivialLocus X.hom (specOver k R) N g) (x : T') :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra R K),
      RingHom.ker (algebraMap R K) = (g x).asIdeal ∧
        isoLocus X.hom (specOver k R) N (LineBundle.trivial _) (specMap R K) := by
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).IsMultiplicative :=
    { id_mem := fun _ ↦ ⟨inferInstance, inferInstance⟩
      comp_mem := fun f g hf hg ↦ by
        have := hf.1
        have := hf.2
        have := hg.1
        have := hg.2
        exact ⟨inferInstance, inferInstance⟩ }
  have hg' : (isoLocus X.hom (specOver k R) N (LineBundle.trivial _)).pullback g ∈
      Scheme.fppfTopology T' := hg
  obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff
    (P := (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))).mp hg'
  obtain ⟨i, x', rfl⟩ := 𝒰.exists_eq x
  have hi : isoLocus X.hom (specOver k R) N (LineBundle.trivial _) (𝒰.f i ≫ g) :=
    hle _ _ (Presieve.ofArrows.mk i)
  let κ := (𝒰.X i).residueField x'
  let h₀ : Spec κ ⟶ Spec (.of R) := (𝒰.X i).fromSpecResidueField x' ≫ 𝒰.f i ≫ g
  have hh₀ : isoLocus X.hom (specOver k R) N (LineBundle.trivial _) h₀ :=
    (isoLocus X.hom (specOver k R) N (LineBundle.trivial _)).downward_closed hi _
  let φ : CommRingCat.of R ⟶ κ := Spec.preimage h₀
  let : Algebra R κ := φ.hom.toAlgebra
  have hspec : specMap R κ = h₀ := by
    change Spec.map (CommRingCat.ofHom φ.hom) = h₀
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨κ, inferInstance, inferInstance, ?_, hspec ▸ hh₀⟩
  obtain ⟨s⟩ : Nonempty (Spec κ) := inferInstanceAs (Nonempty (PrimeSpectrum κ))
  have hx : g (𝒰.f i x') = h₀ s := by
    change _ = g (𝒰.f i (((𝒰.X i).fromSpecResidueField x') s))
    rw [Scheme.fromSpecResidueField_apply]
  rw [hx, ← hspec]
  change RingHom.ker φ.hom = Ideal.comap φ.hom s.asIdeal
  rw [show s.asIdeal = ⊥ from Ideal.eq_bot_of_prime _, ← RingHom.ker_eq_comap_bot]

open Langlands.LinearAlgebra.KernelColumnSplit in
/-- At every point in the image of a member of the triviality locus, the matrix of a two-term
complex computing the sections of the base changes of `N` has a column split with `a` remaining
columns whose scalar does not vanish at that point. -/
theorem exists_columnSplit_of_mem_trivialLocus {a : ℕ} (ha : SectionsRank X a) {R : Type u}
    [CommRing R] [Algebra k R] {N : LineBundle ((relativeSpace X.hom).obj (specOver k R))}
    (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ε : SectionsEquivs X N G)
    {T' : Scheme.{u}} {g : T' ⟶ Spec (.of R)} (hg : trivialLocus X.hom (specOver k R) N g)
    (x : T') : ∃ S : ColumnSplit G.d, Fintype.card S.α = a ∧ S.t ∉ (g x).asIdeal := by
  obtain ⟨K, _, _, hker, hK⟩ := exists_field_of_mem_trivialLocus X hg x
  let : Algebra k K := ((algebraMap R K).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨e⟩ := ha R N K hK
  have hrank : Module.finrank K (LinearMap.ker (G.d.baseChange K)) = a := by
    rw [LinearEquiv.finrank_eq ((ε K).symm.trans e), Module.finrank_fin_fun]
  obtain ⟨S, hS, hcard⟩ := exists_columnSplit (K := K) G.d
  refine ⟨S, hcard.trans hrank, fun h => hS ?_⟩
  rw [← RingHom.mem_ker, hker]
  exact h

end Langlands.AlgebraicGeometry.Picard.RelativePicard

namespace Langlands.AlgebraicGeometry.Picard

/-! ### Sieves of morphisms factoring through a monomorphism -/

/-- The sieve of morphisms factoring through `ι`. -/
def factorSieve {Y Z : Scheme.{u}} (ι : Z ⟶ Y) : Sieve Y where
  arrows _ g := ∃ k, k ≫ ι = g
  downward_closed := by
    rintro _ _ _ ⟨k, rfl⟩ h
    exact ⟨h ≫ k, Category.assoc _ _ _⟩

lemma cutsOut_factorSieve {Y Z : Scheme.{u}} (ι : Z ⟶ Y) : CutsOut ι (factorSieve ι) :=
  fun _ _ => Iff.rfl

/-- The sieve of morphisms factoring through a monomorphism is closed for the fppf topology,
which is subcanonical. -/
lemma factorSieve_isClosed {Y Z : Scheme.{u}} (ι : Z ⟶ Y) [Mono ι] :
    Scheme.fppfTopology.IsClosed (factorSieve ι) := fun _ g hg =>
  FppfClosedLocusDescent.exists_lift_of_covering Scheme.fppfTopology ι g _ hg fun _ _ hu => hu

/-- The fppf closure of a sieve `G` lies in an fppf-closed sieve `F` as soon as every member
of `G` with affine source lies in `F`. -/
lemma close_le_of_forall_spec {Y : Scheme.{u}} {F G : Sieve Y}
    (hF : Scheme.fppfTopology.IsClosed F)
    (h : ∀ (A : CommRingCat.{u}) (g : Spec A ⟶ Y), G g → F g) :
    Scheme.fppfTopology.close G ≤ F := by
  have hGF : G ≤ F := by
    intro W g hg
    apply hF g
    let 𝒰 := W.affineOpenCover
    refine Scheme.fppfTopology.superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck
        (R := Presieve.ofArrows (fun i => Spec (𝒰.X i)) 𝒰.f) ?_)
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact h _ _ (G.downward_closed hg _)
    · rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
      exact ⟨fun x => ⟨𝒰.idx x, 𝒰.covers x⟩, fun i => ⟨inferInstance, inferInstance⟩⟩
  intro W g hg
  exact hF g (Scheme.fppfTopology.superset_covering (Sieve.pullback_monotone g hGF) hg)

namespace RelativePicard

open Langlands.LinearAlgebra.KernelColumnSplit

/-! ### Strata of column splits -/

section Stratum

variable {B : Type u} [CommRing B] {M₀ M₁ : Type*} [AddCommGroup M₀] [Module B M₀]
  [AddCommGroup M₁] [Module B M₁] {d : M₀ →ₗ[B] M₁}

/-- The ideal generated by the entries of the Schur complement of a column split, in the
localization at its scalar. -/
def stratumIdeal (S : ColumnSplit d) : Ideal (Localization.Away S.t) :=
  Ideal.span (Set.range fun p : S.ι × S.α =>
    algebraMap B (Localization.Away S.t) (S.schurMatrix p.1 p.2))

/-- The coordinate ring of the stratum of a column split: the scalar is inverted and the Schur
complement vanishes. -/
abbrev Stratum (S : ColumnSplit d) : Type u :=
  Localization.Away S.t ⧸ stratumIdeal S

lemma isImmersion_specMap_stratum (S : ColumnSplit d) : IsImmersion (specMap B (Stratum S)) := by
  rw [← FrameCombination.specMap_comp B (Localization.Away S.t) (Stratum S)]
  have := IsOpenImmersion.of_isLocalization (S := Localization.Away S.t) S.t
  have : IsClosedImmersion (specMap (Localization.Away S.t) (Stratum S)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

end Stratum

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

/-- Members of the triviality locus landing where the scalar of a column split with `a`
remaining columns is invertible factor through the stratum of the split. -/
theorem factorSieve_stratum_of_mem_trivialLocus {a : ℕ} (ha : SectionsRank X a) {B : Type u}
    [CommRing B] [Algebra k B] {N : LineBundle ((relativeSpace X.hom).obj (specOver k B))}
    (G : CoherentBaseChange.TwoTermComplex.{u, u} B) (ε : SectionsEquivs X N G)
    (S : ColumnSplit G.d) (hS : Fintype.card S.α = a) {T' : Scheme.{u}}
    {g : T' ⟶ Spec (.of B)} (hg : trivialLocus X.hom (specOver k B) N g)
    (ht : factorSieve (specMap B (Localization.Away S.t)) g) :
    factorSieve (specMap B (Stratum S)) g := by
  have := isImmersion_specMap_stratum S
  let L := isoLocus X.hom (specOver k B) N (LineBundle.trivial _)
  let D := factorSieve (specMap B (Localization.Away S.t))
  have key : Scheme.fppfTopology.close (L ⊓ D) ≤ factorSieve (specMap B (Stratum S)) := by
    refine close_le_of_forall_spec (factorSieve_isClosed _) fun A g' ⟨hL, hD⟩ => ?_
    obtain ⟨h, rfl⟩ := hD
    let ψ : CommRingCat.of (Localization.Away S.t) ⟶ A := Spec.preimage h
    let : Algebra (Localization.Away S.t) A := ψ.hom.toAlgebra
    let : Algebra B A := (ψ.hom.comp (algebraMap B (Localization.Away S.t))).toAlgebra
    have : IsScalarTower B (Localization.Away S.t) A := .of_algebraMap_eq fun _ => rfl
    let : Algebra k A := ((algebraMap B A).comp (algebraMap k B)).toAlgebra
    have : IsScalarTower k B A := .of_algebraMap_eq fun _ => rfl
    have hψ : specMap (Localization.Away S.t) A = h := by
      change Spec.map (CommRingCat.ofHom ψ.hom) = h
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have hgA : specMap B A = h ≫ specMap B (Localization.Away S.t) := by
      rw [← FrameCombination.specMap_comp B (Localization.Away S.t) A, hψ]
    rw [← hgA] at hL
    obtain ⟨e⟩ := ha B N A hL
    have htA : IsUnit (algebraMap B A S.t) :=
      (IsLocalization.Away.algebraMap_isUnit S.t).map ψ.hom
    have h0 := S.schurMatrix_map_eq_zero htA ((ε A).symm.trans
      (e.trans (LinearEquiv.funCongrLeft A A (Fintype.equivFinOfCardEq hS))))
    have hI : stratumIdeal S ≤ RingHom.ker ψ.hom := by
      rw [stratumIdeal, Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have := congrFun (congrFun h0 i) j
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact RingHom.mem_ker.mpr this
    let ψ' : CommRingCat.of (Stratum S) ⟶ A :=
      CommRingCat.ofHom (Ideal.Quotient.lift _ ψ.hom hI)
    have hψ' : CommRingCat.ofHom (algebraMap (Localization.Away S.t) (Stratum S)) ≫ ψ' = ψ := by
      ext x
      rfl
    refine ⟨Spec.map ψ', ?_⟩
    rw [← FrameCombination.specMap_comp B (Localization.Away S.t) (Stratum S), ← Category.assoc]
    congr 1
    rw [specMap, ← Spec.map_comp, hψ', Spec.map_preimage]
  apply key
  change Sieve.pullback g (L ⊓ D) ∈ _
  rw [Sieve.pullback_inter, Sieve.pullback_eq_top_of_mem _ ht, inf_top_eq]
  exact hg

end RelativePicard

end Langlands.AlgebraicGeometry.Picard
