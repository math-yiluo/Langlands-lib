import Langlands.GroupScheme.Derived.CentralIntersection.Unipotence
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Central closed subgroups of an actual derived subgroup over an algebraically closed field

Let `G` be an affine group scheme locally of finite type over an algebraically closed field `K`
with trivial unipotent radical, `d : D ⟶ G` an actual derived subgroup, and `s : S ⟶ D` a
closed subgroup whose points are central in `G`. The identity component `H` of the reduced
subgroup of `S` is smooth, connected and central in `G`; in a closed linear embedding of `G`
every eigenvalue of a rational point of `H` is a root of unity of bounded order, so `H` is
unipotent, hence trivial. Since `H` is open in `S`, the identity of `S` is an isolated closed
point. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
  AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralIntersection

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A closed subgroup of an actual derived subgroup whose points are central in an affine `G`
with trivial unipotent radical has an isolated closed point. -/
theorem exists_isClosed_isOpen_singleton {G D S : GroupScheme (Spec (CommRingCat.of K))}
    (d : D ⟶ G) (s : S ⟶ D) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : HasTrivialUnipotentRadical G) (hd : IsDerivedSubgroup d) (hs : IsClosedSubgroup s)
    (hc : SubgroupFunctor.range s ≤ (center G).comap d) :
    ∃ x : S.X.left, IsClosed ({x} : Set S.X.left) ∧ IsOpen ({x} : Set S.X.left) := by
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : IsClosedImmersion s.hom.hom.left := hs
  have hsd : IsClosedSubgroup (s ≫ d) := by
    change IsClosedImmersion (s.hom.hom.left ≫ d.hom.hom.left)
    infer_instance
  have : IsClosedImmersion (s ≫ d).hom.hom.left := hsd
  have : LocallyOfFiniteType S.X.hom := by
    rw [← Over.w (s ≫ d).hom.hom]
    infer_instance
  obtain ⟨H, f, hι, hsm, hconn, hopen, -⟩ :=
    ReducedSubgroup.exists_reducedIdentityComponent (s ≫ d) hsd
  have : IsClosedImmersion (f ≫ s ≫ d).hom.hom.left := hι
  have : Mono (f ≫ s ≫ d).hom.hom := Over.mono_of_mono_left _
  -- The points of `H` are central in `G`.
  have hcsd : IsCentral (s ≫ d) := fun T x => by
    have h : (x ≫ s.hom.hom) ≫ d.hom.hom ∈ (center G).carrier T :=
      SubgroupFunctor.le_def.1 hc T (SubgroupFunctor.mem_range.2 ⟨x, rfl⟩)
    rwa [Category.assoc] at h
  have hcent : IsCentral (f ≫ s ≫ d) := hcsd.comp f
  have hnormal : (SubgroupFunctor.range (f ≫ s ≫ d)).IsNormal := by
    intro T g x _ hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    rw [← (commute_of_mem_center (hcent T y) g).eq, mul_inv_cancel_right]
    exact SubgroupFunctor.mem_range.2 ⟨y, rfl⟩
  have hcomm : ∀ h h' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X, Commute h h' := by
    intro h h'
    change h * h' = h' * h
    refine (cancel_mono (f ≫ s ≫ d).hom.hom).1 ?_
    rw [MonObj.mul_comp, MonObj.mul_comp]
    exact (commute_of_mem_center (hcent _ h) _).eq
  -- A closed linear embedding of `G`, restricted to `H`.
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement K G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : IsClosedImmersion (ρ.restrict (f ≫ s ≫ d)).hom.hom.left := by
    change IsClosedImmersion ((f ≫ s ≫ d).hom.hom.left ≫ ρ.hom.hom.left)
    infer_instance
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K H.X.left
      H.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom (f ≫ s ≫ d).hom.hom.left
  have heig : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      ∀ c ∈ ((ρ.restrict (f ≫ s ≫ d)).rationalMatrix h : Matrix (Fin N) (Fin N) K).charpoly.roots,
        c ^ (Fintype.card (Fin N)).factorial = 1 := by
    intro h c hc'
    have hx : h ≫ (f ≫ s ≫ d).hom.hom = (h ≫ f.hom.hom ≫ s.hom.hom) ≫ d.hom.hom := by
      simp only [Category.assoc]
      rfl
    rw [MatrixRepresentation.rationalMatrix_restrict, hx] at hc'
    exact pow_factorial_eq_one_of_mem_roots hd ρ _ (hx ▸ hcent _ h) hc'
  have hunip : IsUnipotent H :=
    isUnipotent_of_eigenvalues (ρ.restrict (f ≫ s ≫ d)) hcomm (Nat.factorial_ne_zero _) heig
  -- Hence `H` is trivial.
  have hbot := hG H (f ≫ s ≫ d) hι hsm hconn hunip hnormal
  have hone : (𝟙 H.X : H.X ⟶ H.X) = 1 := by
    refine (cancel_mono (f ≫ s ≫ d).hom.hom).1 ?_
    have h1 : 𝟙 H.X ≫ (f ≫ s ≫ d).hom.hom ∈
        (SubgroupFunctor.range (f ≫ s ≫ d)).carrier H.X :=
      SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h1
    rw [h1, MonObj.one_comp]
  have hsub : Subsingleton H.X.left := by
    constructor
    intro a b
    have e : ∀ x : H.X.left, x = η[H.X].left ((toUnit H.X).left x) := fun x =>
      congrArg (fun φ : H.X ⟶ H.X => φ.left x) hone
    have hK : ∀ p q : (Spec (CommRingCat.of K) : Scheme), p = q := fun p q =>
      Subsingleton.elim p q
    rw [e a, e b, hK ((toUnit H.X).left a) ((toUnit H.X).left b)]
  -- The image of `H` is the identity point of `S`, which is therefore open.
  set x₀ : S.X.left := η[S.X].left (IsLocalRing.closedPoint K) with hx₀
  have hrange : Set.range f.hom.hom.left = {x₀} := by
    have hf : f.hom.hom.left (η[H.X].left (IsLocalRing.closedPoint K)) = x₀ := by
      change (η[H.X] ≫ f.hom.hom).left _ = _
      rw [IsMonHom.one_hom]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      rw [Subsingleton.elim a (η[H.X].left (IsLocalRing.closedPoint K)), hf]
      rfl
    · rintro rfl
      exact ⟨_, hf⟩
  refine ⟨x₀, ?_, hrange ▸ hopen⟩
  exact (pointEquivClosedPoint S.X.hom ⟨η[S.X].left, Over.w η[S.X]⟩).2

/-- A group scheme locally of finite type and quasi-compact over an algebraically closed field
with an isolated closed point has finitely many points: translations make every closed point
open, so by the Jacobson property every point is closed and open. -/
theorem finite_of_isOpen_singleton {S : GroupScheme (Spec (CommRingCat.of K))}
    [LocallyOfFiniteType S.X.hom] [CompactSpace S.X.left] (x : S.X.left)
    (hxc : IsClosed ({x} : Set S.X.left)) (hxo : IsOpen ({x} : Set S.X.left)) :
    Finite S.X.left := by
  have : JacobsonSpace S.X.left := LocallyOfFiniteType.jacobsonSpace S.X.hom
  have hopen : ∀ y : S.X.left, IsClosed ({y} : Set S.X.left) → IsOpen ({y} : Set S.X.left) := by
    intro y hy
    obtain ⟨β, -, hβ⟩ := ReducedSubgroup.exists_translation S x y hxc hy
    have h : (Scheme.homeoOfIso β) '' {x} = {y} := by
      rw [Set.image_singleton]
      exact congrArg _ hβ
    rw [← h]
    exact (Scheme.homeoOfIso β).isOpenMap _ hxo
  have hall : closedPoints S.X.left = Set.univ := by
    by_contra hne
    obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
    have hZ : IsClosed (closedPoints S.X.left)ᶜ := by
      rw [isClosed_compl_iff, ← (closedPoints S.X.left).biUnion_of_singleton]
      exact isOpen_biUnion fun y hy => hopen y hy
    obtain ⟨w, hw, hw'⟩ := nonempty_inter_closedPoints ⟨z, hz⟩ hZ.isLocallyClosed
    exact hw hw'
  have : DiscreteTopology S.X.left := discreteTopology_iff_isOpen_singleton.2 fun y =>
    hopen y (show y ∈ closedPoints S.X.left from hall ▸ Set.mem_univ y)
  exact finite_of_compact_of_discrete

/-- Over an algebraically closed field, a closed subgroup of an actual derived subgroup whose
points are central in an affine `G` locally of finite type with trivial unipotent radical has
finitely many points. -/
theorem finite_of_isAlgClosed {G D S : GroupScheme (Spec (CommRingCat.of K))}
    (d : D ⟶ G) (s : S ⟶ D) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : HasTrivialUnipotentRadical G) (hd : IsDerivedSubgroup d) (hs : IsClosedSubgroup s)
    (hc : SubgroupFunctor.range s ≤ (center G).comap d) : Finite S.X.left := by
  obtain ⟨x, hxc, hxo⟩ := exists_isClosed_isOpen_singleton d s hG hd hs hc
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : IsClosedImmersion s.hom.hom.left := hs
  have : IsClosedImmersion (s ≫ d).hom.hom.left := by
    change IsClosedImmersion (s.hom.hom.left ≫ d.hom.hom.left)
    infer_instance
  have : LocallyOfFiniteType S.X.hom := by
    rw [← Over.w (s ≫ d).hom.hom]
    infer_instance
  have : IsAffine S.X.left := isAffine_of_isAffineHom (s ≫ d).hom.hom.left
  exact finite_of_isOpen_singleton x hxc hxo

end Langlands.GroupScheme.CentralIntersection
