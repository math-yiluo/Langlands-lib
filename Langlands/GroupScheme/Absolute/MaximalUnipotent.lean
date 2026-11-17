import Langlands.GroupScheme.Reductive.UnipotentRadicalMaximal
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Maximal smooth connected unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {U V G G' : GroupScheme (Spec (CommRingCat.of k))}

/-- A smooth connected unipotent closed subgroup maximal among such subgroups.
This is the local predicate in `AlgClosedQuotientSubgroupImageStatement`. -/
def IsMaximalUnipotentSubgroup (i : U ⟶ G) : Prop :=
  IsClosedSubgroup i ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U ∧
    ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G) (f : U ⟶ V),
      IsClosedSubgroup j → Smooth V.X.hom → ConnectedSpace V.X.left → IsUnipotent V →
        f ≫ j = i → IsIso f

namespace IsMaximalUnipotentSubgroup

variable {i : U ⟶ G}

theorem isClosedSubgroup (hi : IsMaximalUnipotentSubgroup i) : IsClosedSubgroup i := hi.1
theorem smooth (hi : IsMaximalUnipotentSubgroup i) : Smooth U.X.hom := hi.2.1
theorem connectedSpace (hi : IsMaximalUnipotentSubgroup i) : ConnectedSpace U.X.left :=
  hi.2.2.1
theorem isUnipotent (hi : IsMaximalUnipotentSubgroup i) : IsUnipotent U := hi.2.2.2.1

theorem maximal (hi : IsMaximalUnipotentSubgroup i)
    (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G) (f : U ⟶ V) :
    IsClosedSubgroup j → Smooth V.X.hom → ConnectedSpace V.X.left → IsUnipotent V →
      f ≫ j = i → IsIso f := hi.2.2.2.2 V j f

/-- Changing the source presentation preserves maximal unipotence. -/
theorem iso_comp (hi : IsMaximalUnipotentSubgroup i) (e : V ≅ U) :
    IsMaximalUnipotentSubgroup (e.hom ≫ i) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  have : Smooth U.X.hom := hi.smooth
  refine ⟨?_, ?_, ?_, IsUnipotent.of_iso e hi.isUnipotent, ?_⟩
  · change IsClosedImmersion (e.hom.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  · rw [← Over.w e.hom.hom.hom]
    infer_instance
  · exact (Scheme.homeoOfIso ((Over.forget _).mapIso
      ((Grp.forget _).mapIso e))).connectedSpace_iff.mpr hi.connectedSpace
  · intro W j f hj hs hc hu hf
    have : IsIso (e.inv ≫ f) :=
      hi.maximal W j (e.inv ≫ f) hj hs hc hu (by
        rw [Category.assoc, hf, Iso.inv_hom_id_assoc])
    have hfactor : f = e.hom ≫ (e.inv ≫ f) := by simp
    rw [hfactor]
    infer_instance

/-- Changing the ambient group preserves maximal unipotence. -/
theorem comp_iso (hi : IsMaximalUnipotentSubgroup i) (e : G ≅ G') :
    IsMaximalUnipotentSubgroup (i ≫ e.hom) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  have : IsIso e.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e.symm)).hom)
  refine ⟨?_, hi.smooth, hi.connectedSpace, hi.isUnipotent, ?_⟩
  · change IsClosedImmersion (i.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  · intro W j f hj hs hc hu hf
    have : IsClosedImmersion j.hom.hom.left := hj
    apply hi.maximal W (j ≫ e.inv) f
    · change IsClosedImmersion (j.hom.hom.left ≫ e.inv.hom.hom.left)
      infer_instance
    · exact hs
    · exact hc
    · exact hu
    · rw [← Category.assoc, hf, Category.assoc, e.hom_inv_id, Category.comp_id]

end IsMaximalUnipotentSubgroup

namespace MaximalUnipotentExistence

open BorelExistence

/-- An admissible subgroup before maximality is imposed. -/
def IsCandidate (i : U ⟶ G) : Prop :=
  IsClosedSubgroup i ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U

/-- Every prescribed candidate is contained in a maximal one. -/
theorem exists_containing (a : U ⟶ G) (ha : IsCandidate a)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G) (f : U ⟶ V),
      IsMaximalUnipotentSubgroup j ∧ f ≫ j = a := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G) (f : U ⟶ V),
      IsCandidate j ∧ f ≫ j = a ∧ (coordinateKernel j).height.toNat = n
  have hP : ∃ n, P n := ⟨_, U, a, 𝟙 U, ha, Category.id_comp a, rfl⟩
  obtain ⟨V, j, f, hj, hf, hheight⟩ := Nat.find_spec hP
  obtain ⟨hjc, hjs, hjconn, hju⟩ := hj
  refine ⟨V, j, f, ⟨hjc, hjs, hjconn, hju, ?_⟩, hf⟩
  intro W l g hlc hls hlconn hlu hg
  have := hjs
  have := hjconn
  have := hls
  have := hlconn
  apply isIso_of_coordinateKernel_height_le j l g hjc hlc hg
  have hmin : (coordinateKernel j).height.toNat ≤ (coordinateKernel l).height.toNat := by
    rw [hheight]
    exact Nat.find_min' hP
      ⟨W, l, f ≫ g, ⟨hlc, hls, hlconn, hlu⟩, by rw [Category.assoc, hg, hf], rfl⟩
  rw [← ENat.natCast_toNat (coordinateKernel_height_ne_top j),
    ← ENat.natCast_toNat (coordinateKernel_height_ne_top l)]
  exact_mod_cast hmin

/-- Every affine group locally of finite type over a field has a maximal smooth
connected unipotent subgroup. -/
theorem exists_maximal (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
      IsMaximalUnipotentSubgroup i := by
  obtain ⟨U, i, _, hi, _⟩ := exists_containing
    (0 : Grp.trivial (Over (Spec (CommRingCat.of k))) ⟶ G)
    ⟨(UnipotentRadicalExistence.trivial_isCandidate G).isClosedSubgroup,
      (UnipotentRadicalExistence.trivial_isCandidate G).smooth,
      (UnipotentRadicalExistence.trivial_isCandidate G).connectedSpace,
      UnipotentRadicalExistence.trivial_isUnipotent⟩
  exact ⟨U, i, hi⟩

end MaximalUnipotentExistence

end Langlands.GroupScheme
