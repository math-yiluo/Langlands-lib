import Langlands.GroupScheme.Torus.ExistenceStatement
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.SplitMono
import Langlands.GroupScheme.Rational.SplitTorusFiniteRank
import Langlands.GroupScheme.Rational.WeightSupportVanishing
import Langlands.GroupScheme.Lie.ScalarExtension
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Proof: maximal tori over the original field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace TorusExistence

/-! ### Base change along a field extension -/

section Instances

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Extending the field keeps the structure morphism affine. -/
theorem isAffineHom_baseChange [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- Extending the field keeps the structure morphism locally of finite type. -/
theorem locallyOfFiniteType_baseChange [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

end Instances

attribute [local instance] isAffineHom_baseChange locallyOfFiniteType_baseChange

/-! ### A bound for the ranks of closed tori -/

section Bound

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The dimension of the actual Lie kernel does not change under extension of the field. -/
theorem finrank_lieKernel_baseChange (K : Type u) [Field K] [Algebra k K] :
    Module.finrank K
        (Additive (lieKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) K)) =
      Module.finrank k (Additive (lieKernel G k)) := by
  rw [(Lie.kernelBaseChangeLinearEquiv k K G K).finrank_eq,
    ← (Lie.kernelScalarExtension G K).finrank_eq, Module.finrank_baseChange]

/-- If a closed subgroup `T` of `G` becomes isomorphic to `𝔾_m^I` over some extension field,
then `|I|` is at most the dimension of the Lie kernel of `G`. -/
theorem card_le_finrank {T : GroupScheme (Spec (CommRingCat.of k))} (i : T ⟶ G)
    (hi : IsClosedSubgroup i) (K : Type u) [Field K] [Algebra k K] (I : Type u) [Finite I]
    (e : (GroupScheme.baseChange (algebraBaseMap k K)).obj T ≅
      splitTorus (Spec (CommRingCat.of K)) I) :
    Nat.card I ≤ Module.finrank k (Additive (lieKernel G k)) := by
  have := Lie.finiteDimensional_lieKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
  rw [← finrank_lieKernel_baseChange G K]
  exact splitTorus.card_le_finrank_lieKernel I
    (e.inv ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (IsClosedSubgroup.iso_comp e.symm (hi.baseChange _))

end Bound

/-! ### Splittings over larger fields -/

section Transfer

/-- A splitting over `S'` gives a splitting with the same index type over any `S''` mapping
to `S'`. -/
theorem nonempty_splitIso_of_comp {S S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S')
    {d : S'' ⟶ S} (h : c ≫ b = d) (T : GroupScheme S) (I : Type u) [Finite I]
    (e : (GroupScheme.baseChange b).obj T ≅ splitTorus S' I) :
    Nonempty ((GroupScheme.baseChange d).obj T ≅ splitTorus S'' I) := by
  subst h
  exact ⟨(Functor.mapGrpNatIso (Over.pullbackComp c b)).app T ≪≫
    Functor.mapGrpCompIso.app T ≪≫ (GroupScheme.baseChange c).mapIso e ≪≫
    splitTorus.baseChangeIso c I⟩

variable {k : Type u} [Field k]

/-- A splitting over `K` gives a splitting with the same index type over any field `E`
receiving a `k`-embedding of `K`. -/
theorem nonempty_splitIso_extension {K E : Type u} [Field K] [Field E] [Algebra k K]
    [Algebra k E] (φ : K →+* E) (hφ : φ.comp (algebraMap k K) = algebraMap k E)
    (T : GroupScheme (Spec (CommRingCat.of k))) (I : Type u) [Finite I]
    (e : (GroupScheme.baseChange (algebraBaseMap k K)).obj T ≅
      splitTorus (Spec (CommRingCat.of K)) I) :
    Nonempty ((GroupScheme.baseChange (algebraBaseMap k E)).obj T ≅
      splitTorus (Spec (CommRingCat.of E)) I) :=
  nonempty_splitIso_of_comp (algebraBaseMap k K) (Spec.map (CommRingCat.ofHom φ))
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]) T I e

end Transfer

/-! ### Isomorphisms descend along field extensions -/

section Descent

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]

/-- A field extension is faithfully flat, so its base morphism is flat and surjective. -/
theorem flat_and_surjective_algebraBaseMap :
    Flat (algebraBaseMap k K) ∧ Surjective (algebraBaseMap k K) :=
  (flat_and_surjective_SpecMap_iff _).2 (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance)

/-- The base morphism of a field extension is flat. -/
theorem flat_algebraBaseMap : Flat (algebraBaseMap k K) :=
  (flat_and_surjective_algebraBaseMap K).1

/-- The base morphism of a field extension is surjective. -/
theorem surjective_algebraBaseMap : Surjective (algebraBaseMap k K) :=
  (flat_and_surjective_algebraBaseMap K).2

attribute [local instance] flat_algebraBaseMap surjective_algebraBaseMap

/-- A homomorphism of group schemes over `k` is an isomorphism if it becomes one after
extending the field to `K`. -/
theorem isIso_of_isIso_baseChange {H G : GroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange (algebraBaseMap k K)).map f)] : IsIso f := by
  have houter : IsPullback
      (((GroupScheme.baseChange (algebraBaseMap k K)).map f).hom.hom.left ≫
        pullback.snd G.X.hom (algebraBaseMap k K))
      (pullback.fst H.X.hom (algebraBaseMap k K)) (algebraBaseMap k K)
      (f.hom.hom.left ≫ G.X.hom) := by
    change IsPullback (((Over.pullback (algebraBaseMap k K)).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback H.X.hom (algebraBaseMap k K)).flip
  have hp := houter.of_right
    (show ((GroupScheme.baseChange (algebraBaseMap k K)).map f).hom.hom.left ≫
        pullback.fst G.X.hom (algebraBaseMap k K) =
        pullback.fst H.X.hom (algebraBaseMap k K) ≫ f.hom.hom.left by
      change ((Over.pullback (algebraBaseMap k K)).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback G.X.hom (algebraBaseMap k K)).flip
  have hfst : IsIso ((Grp.forget₂Mon _ ⋙ Mon.forget _ ⋙ Over.forget _).map
      ((GroupScheme.baseChange (algebraBaseMap k K)).map f)) := inferInstance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (pullback.fst G.X.hom (algebraBaseMap k K)) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : IsIso f.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms _)
      (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)) hp hQ hfst
  have : IsIso ((Over.forget _).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map f.hom) := ‹IsIso f.hom.hom›
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := ‹IsIso f.hom›
  exact isIso_of_reflects_iso f (Grp.forget₂Mon _)

end Descent

/-! ### The trivial torus -/

section Trivial

variable {S : Scheme.{u}}

/-- The split torus on the empty index type is the trivial group scheme. -/
def splitTorusEmptyIso : splitTorus S PEmpty.{u + 1} ≅ Grp.trivial (Over S) :=
  isoOfPointModels (fun _ : Over S => PUnit.{u + 1}) (fun _ => 1)
    (fun T => (splitTorus.pointsEquiv PEmpty T).trans MulEquiv.ofUnique)
    (fun T => @MulEquiv.ofUnique _ _ ⟨⟨CartesianMonoidalCategory.toUnit T⟩,
      fun x => CartesianMonoidalCategory.toUnit_unique x _⟩ _ _ _)
    (fun _ _ => Subsingleton.elim _ _) (fun _ _ => Subsingleton.elim _ _)

variable (k : Type u) [Field k]

/-- The trivial torus over `k`: the split torus on the empty index type. -/
abbrev trivialTorus : CommGroupScheme (Spec (CommRingCat.of k)) :=
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) PEmpty.{u + 1}

/-- The trivial torus is a torus. -/
theorem isTorus_trivialTorus : IsTorus (trivialTorus k).toGrp :=
  (isSplitTorus_splitTorus _).isTorus

variable {k} (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The inclusion of the trivial torus as the identity section. -/
def trivialTorusHom : (trivialTorus k).toGrp ⟶ G :=
  splitTorusEmptyIso.hom ≫ kernelUnit G

/-- The identity section of a separated group scheme embeds the trivial torus as a closed
subgroup. -/
theorem isClosedSubgroup_trivialTorusHom [IsSeparated G.X.hom] :
    IsClosedSubgroup (trivialTorusHom G) :=
  IsClosedSubgroup.iso_comp splitTorusEmptyIso (kernelUnit_isClosedSubgroup G)

/-- Every separated group scheme over a field has a closed torus, namely the trivial one. -/
theorem exists_closedTorus [IsSeparated G.X.hom] :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsTorus T.toGrp ∧ IsClosedSubgroup i :=
  ⟨trivialTorus k, trivialTorusHom G, isTorus_trivialTorus k,
    isClosedSubgroup_trivialTorusHom G⟩

end Trivial

/-! ### Closed tori of maximal rank -/

section Main

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))

/-- `n` is the cardinality of the index type of a splitting, over some extension field, of
some closed subgroup of `G`. -/
def IsClosedTorusRank (n : ℕ) : Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G), IsClosedSubgroup i ∧
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (I : Type u) (_ : Finite I),
      Nonempty ((GroupScheme.baseChange (algebraBaseMap k K)).obj T.toGrp ≅
        splitTorus (Spec (CommRingCat.of K)) I) ∧ Nat.card I = n

/-- Every smooth affine group scheme over a field has a maximal torus over that field. -/
theorem exists_isMaximalTorus [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G), IsMaximalTorus i := by
  classical
  let N := Module.finrank k (Additive (lieKernel G k))
  have hbound : ∀ n, IsClosedTorusRank G n → n ≤ N := by
    rintro n ⟨T, i, hi, K, _, _, I, _, ⟨e⟩, rfl⟩
    exact card_le_finrank G i hi K I e
  have h0 : IsClosedTorusRank G 0 :=
    ⟨trivialTorus k, trivialTorusHom G, isClosedSubgroup_trivialTorusHom G, k, inferInstance,
      inferInstance, PEmpty, inferInstance,
      ⟨splitTorus.baseChangeIso (algebraBaseMap k k) PEmpty⟩, by simp⟩
  obtain ⟨T, i, hi, K, _, _, I, _, ⟨e⟩, hI⟩ :=
    Nat.findGreatest_spec (P := IsClosedTorusRank G) (Nat.zero_le N) h0
  refine ⟨T, i, ⟨K, inferInstance, inferInstance, I, inferInstance, ⟨e⟩⟩, hi, ?_⟩
  intro T' i' f hT' hi' hf
  obtain ⟨K', _, _, I', _, ⟨e'⟩⟩ := hT'
  have hrank' : IsClosedTorusRank G (Nat.card I') :=
    ⟨T', i', hi', K', inferInstance, inferInstance, I', inferInstance, ⟨e'⟩, rfl⟩
  have hI' : Nat.card I' ≤ Nat.card I :=
    hI ▸ Nat.le_findGreatest (hbound _ hrank') hrank'
  let E := TorusBaseChange.commonExtension k K K'
  let : Field E.carrier := E.field
  let : Algebra k E.carrier := (E.leftHom.comp (algebraMap k K)).toAlgebra
  obtain ⟨eE⟩ := nonempty_splitIso_extension E.leftHom rfl T.toGrp I e
  obtain ⟨eE'⟩ := nonempty_splitIso_extension E.rightHom E.compatible.symm T'.toGrp I' e'
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono f.hom.hom := by
    have hc : f.hom.hom ≫ i'.hom.hom = i.hom.hom := congrArg (fun g => g.hom.hom) hf
    exact mono_of_mono_fac hc
  have hmono : Mono ((GroupScheme.baseChange (algebraBaseMap k E.carrier)).map f).hom.hom := by
    change Mono ((Over.pullback _).map f.hom.hom)
    infer_instance
  have := splitTorus.isIso_of_mono_of_iso eE eE' _ hmono hI'
  exact isIso_of_isIso_baseChange E.carrier f

end Main

end TorusExistence

/-- Every smooth affine group scheme over a field has a maximal torus over that field. -/
theorem maximalTorusExistence : MaximalTorusExistenceStatement.{u} :=
  fun _ _ G _ _ => TorusExistence.exists_isMaximalTorus G

end Langlands.GroupScheme
