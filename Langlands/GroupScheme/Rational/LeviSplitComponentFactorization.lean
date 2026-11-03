import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Torus.SplitMono

/-! # Split components of dynamic Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A closed subgroup of a group scheme with affine structure morphism has affine structure
morphism. -/
theorem IsClosedSubgroup.isAffineHom_source {S : Scheme.{u}} {M G : GroupScheme S} {j : M ⟶ G}
    (hj : IsClosedSubgroup j) [IsAffineHom G.X.hom] : IsAffineHom M.X.hom := by
  have : IsClosedImmersion j.hom.hom.left := hj
  rw [← Over.w j.hom.hom]
  infer_instance

/-- A closed subgroup between split tori, presented by isomorphisms with standard split tori,
cannot decrease the number of factors. -/
theorem card_le_of_isClosedSubgroup_of_iso {A B : GroupScheme (Spec (CommRingCat.of k))}
    {I J : Type u} [Finite I] [Finite J] (eA : A ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (eB : B ≅ splitTorus (Spec (CommRingCat.of k)) J) (f : A ⟶ B) (hf : IsClosedSubgroup f) :
    Nat.card I ≤ Nat.card J :=
  splitTorus.card_le_card_of_isClosedSubgroup I J (eA.inv ≫ f ≫ eB.hom)
    (IsClosedSubgroup.iso_comp eA.symm (hf.comp_iso eB))

/-- If every central split torus of `M` factors through a fixed closed split subtorus
`t : T ⟶ M`, and `M` has some central split torus, then `M` has a split component: a central
split torus of maximal dimension. -/
theorem exists_isSplitComponent_of_factor {M : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ M} (htc : IsClosedSubgroup t)
    (hT : IsSplitTorus T.toGrp)
    (hfac : ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
      IsCentralSplitTorus a → ∃ g : A.toGrp ⟶ T.toGrp, g ≫ t = a)
    {A₀ : CommGroupScheme (Spec (CommRingCat.of k))} {a₀ : A₀.toGrp ⟶ M}
    (h₀ : IsCentralSplitTorus a₀) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M), IsSplitComponent a := by
  classical
  obtain ⟨IT, hIT, ⟨eT⟩⟩ := hT
  let P : ℕ → Prop := fun n => ∃ (A : CommGroupScheme (Spec (CommRingCat.of k)))
    (a : A.toGrp ⟶ M) (I : Type u) (_ : Finite I)
    (_ : A.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I), IsCentralSplitTorus a ∧ Nat.card I = n
  have hbound : ∀ n, P n → n ≤ Nat.card IT := by
    rintro n ⟨A, a, I, hI, eA, ha, rfl⟩
    obtain ⟨g, hg⟩ := hfac A a ha
    exact card_le_of_isClosedSubgroup_of_iso eA eT g (IsClosedSubgroup.of_comp htc (by rw [hg]; exact ha.1.2))
  obtain ⟨I₀, hI₀, ⟨e₀⟩⟩ := h₀.1.1
  have hP₀ : P (Nat.card I₀) := ⟨A₀, a₀, I₀, hI₀, e₀, h₀, rfl⟩
  have hPN : P (Nat.findGreatest P (Nat.card IT)) :=
    Nat.findGreatest_spec (hbound _ hP₀) hP₀
  obtain ⟨A, a, I, hI, eA, ha, hN⟩ := hPN
  refine ⟨A, a, ha, fun A' a' ha' f hf => ?_⟩
  obtain ⟨I', hI', ⟨eA'⟩⟩ := ha'.1.1
  have hfc : IsClosedSubgroup f := IsClosedSubgroup.of_comp ha'.1.2 (by rw [hf]; exact ha.1.2)
  have hle : Nat.card I' ≤ Nat.card I := by
    rw [hN]
    exact Nat.le_findGreatest (hbound _ ⟨A', a', I', hI', eA', ha', rfl⟩)
      ⟨A', a', I', hI', eA', ha', rfl⟩
  have : IsClosedImmersion f.hom.hom.left := hfc
  exact splitTorus.isIso_of_mono_of_iso eA eA' f (Over.mono_of_mono_left _) hle

/-- The split-component part of Renard V.3.6 for an actual dynamic Levi subgroup: for a closed
representative `j : M ⟶ G` of the centralizer of `ν ≫ i`, where `i : T ⟶ G` is a maximal split
torus of an affine `G`, every split component `A_G` of `G` factors through a split component
`A_M` of `M` that factors through `T`, compatibly with character restriction. -/
theorem leviSplitComponent_factorization {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hT : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    {M : GroupScheme (Spec (CommRingCat.of k))} {j : M ⟶ G} (hjc : IsClosedSubgroup j)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    {A_G : CommGroupScheme (Spec (CommRingCat.of k))} {iG : A_G.toGrp ⟶ G}
    (hG : IsSplitComponent iG) :
    ∃ (A_M : CommGroupScheme (Spec (CommRingCat.of k))) (iM : A_M.toGrp ⟶ M)
      (f : A_G.toGrp ⟶ A_M.toGrp) (g : A_M.toGrp ⟶ T.toGrp),
      IsSplitComponent iM ∧ f ≫ iM ≫ j = iG ∧ g ≫ i = iM ≫ j ∧
        (characterRestrict f).comp ((characterRestrict iM).comp (characterRestrict j)) =
          characterRestrict iG := by
  have : IsAffineHom M.X.hom := hjc.isAffineHom_source
  let t := Dynamic.torusFactor i (CommGroupScheme.groupHom ν) hj
  have ht : t ≫ j = i := Dynamic.torusFactor_comp i _ hj
  have htmax : IsMaximalSplitTorus (t ≫ j) := by rw [ht]; exact hT
  have htc : IsClosedSubgroup t := IsClosedSubgroup.of_comp hjc (by rw [ht]; exact hT.1.2)
  have hfac : ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
      IsCentralSplitTorus a → ∃ g : A.toGrp ⟶ T.toGrp, g ≫ t = a :=
    fun _ _ ha => ha.exists_factor_of_isMaximalSplitTorus hjc htmax
  let aG := Dynamic.centralizerFactor _ hj iG hG.1.2
  have haG : aG ≫ j = iG := Dynamic.centralizerFactor_comp _ hj iG hG.1.2
  have haGc : IsCentralSplitTorus aG :=
    hG.1.isCentralSplitTorus_centralizerFactor _ hj hjc
  obtain ⟨A_M, iM, hM⟩ := exists_isSplitComponent_of_factor htc hT.1.1 hfac haGc
  obtain ⟨f, hf⟩ := hM.exists_factor hG.1.1.1 haGc.2
  obtain ⟨g, hg⟩ := hfac A_M iM hM.1
  have hfj : f ≫ iM ≫ j = iG := by rw [← Category.assoc, hf, haG]
  refine ⟨A_M, iM, f, g, hM, hfj, ?_, characterRestrict_chain f iM j iG hfj⟩
  rw [← ht, ← Category.assoc, hg]

end Langlands.GroupScheme
