import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Mathlib.RingTheory.Jacobson.Artinian

/-! # Finite centres from the absence of smooth connected central subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every smooth connected closed central subgroup has trivial range on all
test schemes. This predicate does not assert existence of a centre. -/
def HasTrivialSmoothConnectedCentralSubgroups {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
    IsClosedSubgroup h → Smooth H.X.hom → ConnectedSpace H.X.left →
    IsCentral h → SubgroupFunctor.range h = ⊥

namespace FiniteCenterOfNoCentralSubgroups

variable {k : Type u} [Field k]

/-- A discrete affine scheme of finite type over a field is finite, including
its nilpotent structure. -/
theorem isFinite_of_discrete {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsAffineHom f] [LocallyOfFiniteType f] [DiscreteTopology X] :
    IsFinite f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let e := Scheme.ΓSpecIso (CommRingCat.of k)
  let φ : CommRingCat.of k ⟶ Γ(X, ⊤) := e.inv ≫ f.appTop
  let : Algebra k Γ(X, ⊤) := φ.hom.toAlgebra
  have hft : f.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  have hφft : φ.hom.FiniteType :=
    hft.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso e.inv).2)
  have : Algebra.FiniteType k Γ(X, ⊤) := hφft
  have : DiscreteTopology (PrimeSpectrum Γ(X, ⊤)) :=
    X.isoSpec.inv.homeomorph.isEmbedding.discreteTopology
  have : Ring.KrullDimLE 0 Γ(X, ⊤) :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp
      (inferInstance : DiscreteTopology (PrimeSpectrum Γ(X, ⊤)))).2
  have hφ : φ.hom.Finite :=
    (Module.finite_iff_krullDimLE_zero k Γ(X, ⊤)).mpr inferInstance
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
  refine ⟨inferInstance, ?_⟩
  have he : e.hom ≫ φ = f.appTop := by
    dsimp [φ]
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  rw [← he]
  exact hφ.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso e.hom).2)

variable [IsAlgClosed k]

/-- An affine field group whose underlying space contains an open singleton
is finite. Translations and the Jacobson property account for every point. -/
theorem isFinite_of_open_singleton
    (Z : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom Z.X.hom] [LocallyOfFiniteType Z.X.hom]
    (z : Z.X.left) (hz : IsOpen ({z} : Set Z.X.left)) : IsFinite Z.X.hom := by
  have : JacobsonSpace Z.X.left := LocallyOfFiniteType.jacobsonSpace Z.X.hom
  have hzc : IsClosed ({z} : Set Z.X.left) :=
    isClosed_singleton_of_isLocallyClosed_singleton hz.isLocallyClosed
  have hopen : ∀ x : Z.X.left, IsClosed ({x} : Set Z.X.left) →
      IsOpen ({x} : Set Z.X.left) := by
    intro x hx
    obtain ⟨β, -, hβ⟩ := ReducedSubgroup.exists_translation Z z x hzc hx
    rw [← hβ, ← Set.image_singleton]
    exact β.hom.homeomorph.isOpenMap _ hz
  have hcp : IsOpen (closedPoints Z.X.left) := by
    rw [← (closedPoints Z.X.left).biUnion_of_singleton]
    exact isOpen_biUnion fun x hx => hopen x hx
  have hall : closedPoints Z.X.left = Set.univ := by
    have h := closure_inter_closedPoints hcp.isClosed_compl
    rw [Set.compl_inter_self, closure_empty] at h
    apply compl_injective
    simpa using h.symm
  have : DiscreteTopology Z.X.left :=
    discreteTopology_iff_isOpen_singleton.mpr fun x =>
      hopen x (show x ∈ closedPoints Z.X.left by rw [hall]; trivial)
  exact isFinite_of_discrete Z.X.hom

end FiniteCenterOfNoCentralSubgroups

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G Z : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- If every smooth connected closed central subgroup is trivial, every full
scheme-theoretic centre representative is finite, without discarding nilpotents. -/
theorem IsSchemeTheoreticCenter.isFinite_of_no_smooth_connected_central_subgroups
    {z : Z ⟶ G} (hz : IsSchemeTheoreticCenter z)
    (hG : HasTrivialSmoothConnectedCentralSubgroups G) :
    IsFinite Z.X.hom := by
  have : IsClosedImmersion z.hom.hom.left := hz.1
  have : Mono z.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  have : LocallyOfFiniteType Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  obtain ⟨H, f, hclosed, hs, hc, hopen, -⟩ :=
    ReducedSubgroup.exists_reducedIdentityComponent z hz.1
  have hcentral : IsCentral (f ≫ z) := by
    intro T x
    simpa only [Grp.comp_hom_hom, ← Category.assoc] using hz.isCentral T (x ≫ f.hom.hom)
  have hbot := hG H (f ≫ z) hclosed hs hc hcentral
  have : IsClosedImmersion (f ≫ z).hom.hom.left := hclosed
  have : Mono (f ≫ z).hom.hom := Over.mono_of_mono_left _
  have hone : (𝟙 H.X : H.X ⟶ H.X) = 1 := by
    apply (cancel_mono (f ≫ z).hom.hom).mp
    have h1 : 𝟙 H.X ≫ (f ≫ z).hom.hom ∈
        (SubgroupFunctor.range (f ≫ z)).carrier H.X :=
      SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h1
    rw [h1, MonObj.one_comp]
  have : Subsingleton H.X.left := by
    constructor
    intro a b
    have he : ∀ x : H.X.left, x = η[H.X].left ((toUnit H.X).left x) :=
      fun x => congrArg (fun φ : H.X ⟶ H.X => φ.left x) hone
    have hK : (toUnit H.X).left a = (toUnit H.X).left b :=
      @Subsingleton.elim (PrimeSpectrum k) _ _ _
    rw [he a, he b, hK]
  have : ConnectedSpace H.X.left := hc
  have : Nonempty H.X.left := inferInstance
  obtain ⟨x⟩ := ‹Nonempty H.X.left›
  have hrange : Set.range f.hom.hom.left = {f.hom.hom.left x} := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact congrArg f.hom.hom.left (Subsingleton.elim w x)
    · rintro rfl
      exact ⟨x, rfl⟩
  rw [hrange] at hopen
  exact FiniteCenterOfNoCentralSubgroups.isFinite_of_open_singleton Z _ hopen

end Langlands.GroupScheme
