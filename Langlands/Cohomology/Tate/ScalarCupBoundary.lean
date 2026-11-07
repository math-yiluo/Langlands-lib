import Langlands.Cohomology.Tate.CupLawsProof
import Langlands.Cohomology.Tate.TateComparisonProof

/-! # Scalar cup products and connecting maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

/-- Scalar multiplication gives a map from the tensor sequence to the original
coefficient sequence. -/
def scalarPairingSequence (S : ShortComplex (Rep.{u} R G)) :
    S.map (MonoidalCategory.tensorRight (Rep.trivial R G R)) ⟶ S where
  τ₁ := (scalarPairing S.X₁).tensorHom
  τ₂ := (scalarPairing S.X₂).tensorHom
  τ₃ := (scalarPairing S.X₃).tensorHom
  comm₁₂ := Pairing.tensorHom_naturality _ _ S.f (𝟙 _) S.f
    (fun a r => map_smul S.f.hom r a)
  comm₂₃ := Pairing.tensorHom_naturality _ _ S.g (𝟙 _) S.g
    (fun a r => map_smul S.g.hom r a)

variable [Fintype G]

/-- Scalar cup products carry the first-variable connecting map to the
connecting map of the original coefficient sequence. -/
lemma scalarCup_delta_first (S : ShortComplex (Rep.{u} R G))
    (hS : S.ShortExact)
    (hT : (S.map (MonoidalCategory.tensorRight (Rep.trivial R G R))).ShortExact)
    (p q : ℤ) (a : tateCohomology S.X₃ p)
    (b : tateCohomology (Rep.trivial R G R) q) :
    cup (scalarPairing S.X₁) (p + 1) q (TateCohomology.δ hS p a) b =
      tateDeltaTo hS (p + q) ((p + 1) + q) (by omega)
        (cup (scalarPairing S.X₃) p q a b) := by
  change (tateCohomologyFunctor ((p + 1) + q)).map (scalarPairing S.X₁).tensorHom
      (tensorCup S.X₁ (Rep.trivial R G R) (p + 1) q (TateCohomology.δ hS p a) b) = _
  rw [tensorCup_delta_first S hS _ hT]
  exact ConcreteCategory.congr_hom
    (tateDeltaTo_naturality hT hS (scalarPairingSequence S)
      (p + q) ((p + 1) + q) (by omega))
    (tensorCup S.X₃ (Rep.trivial R G R) p q a b)

/-- The scalar first-boundary law with a specified successor degree. -/
lemma scalarCup_delta_first_to (S : ShortComplex (Rep.{u} R G))
    (hS : S.ShortExact)
    (hT : (S.map (MonoidalCategory.tensorRight (Rep.trivial R G R))).ShortExact)
    (p m q : ℤ) (h : p + 1 = m) (a : tateCohomology S.X₃ p)
    (b : tateCohomology (Rep.trivial R G R) q) :
    cup (scalarPairing S.X₁) m q (tateDeltaTo hS p m h a) b =
      tateDeltaTo hS (p + q) (m + q) (by omega)
        (cup (scalarPairing S.X₃) p q a b) := by
  subst m
  exact scalarCup_delta_first S hS hT p q a b

/-- The invariant scalar one defines the unit class in degree zero. -/
def scalarUnitClass :
    tateCohomology (Rep.trivial R G R) 0 :=
  zeroClass _ ⟨1, fun _ => rfl⟩

/-- Scalar cup product by the invariant one is the identity, with the degree
equality made explicit. -/
lemma scalarCup_unit (n : ℤ) (b : tateCohomology (Rep.trivial R G R) n) :
    cup (scalarPairing (Rep.trivial R G R)) 0 n (scalarUnitClass (R := R) (G := G)) b =
      (tateDegreeIso _ (show n = 0 + n by omega)).hom b := by
  let T := Rep.trivial R G R
  let a : T.ρ.invariants := ⟨1, fun _ => rfl⟩
  have hid : tensorInvariantLeft T T a ≫ (scalarPairing T).tensorHom = 𝟙 T := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro r
    change r • (1 : R) = r
    exact mul_one r
  change (tateCohomologyFunctor (0 + n)).map (scalarPairing T).tensorHom
      (tensorCup T T 0 n (zeroClass T a) b) = _
  rw [tensorCup_invariantLeft]
  have hnat := ConcreteCategory.congr_hom
    (tateDegreeIso_naturality (scalarPairing T).tensorHom
      (show n = 0 + n by omega))
    ((tateCohomologyFunctor n).map (tensorInvariantLeft T T a) b)
  change (tateCohomologyFunctor (0 + n)).map (scalarPairing T).tensorHom
      ((tateDegreeIso _ _).hom
        ((tateCohomologyFunctor n).map (tensorInvariantLeft T T a) b)) =
    (tateDegreeIso T _).hom
      ((tateCohomologyFunctor n).map (scalarPairing T).tensorHom
        ((tateCohomologyFunctor n).map (tensorInvariantLeft T T a) b)) at hnat
  rw [hnat]
  congr 1
  change (((tateCohomologyFunctor n).map (tensorInvariantLeft T T a) ≫
    (tateCohomologyFunctor n).map (scalarPairing T).tensorHom) b) = b
  rw [← Functor.map_comp, hid, CategoryTheory.Functor.map_id]
  rfl

/-- Vanishing of the middle cohomology follows from surjectivity of the preceding
boundary and injectivity of the following boundary. -/
lemma tate_middle_isZero (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (n : ℤ) (hepi : Epi (TateCohomology.δ hS n))
    (hmono : Mono (TateCohomology.δ hS (n + 1))) :
    IsZero (tateCohomology S.X₂ (n + 1)) := by
  have hf : (tateCohomologyFunctor (n + 1)).map S.f = 0 := by
    rw [← cancel_epi (TateCohomology.δ hS n), TateCohomology.δ_map, comp_zero]
  have hg : (tateCohomologyFunctor (n + 1)).map S.g = 0 := by
    rw [← cancel_mono (TateCohomology.δ hS (n + 1)), TateCohomology.map_δ, zero_comp]
  exact (Comparison.tate_exact₂ hS (n + 1)).isZero_X₂ hf hg

section TwoRows

variable (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    {P : Rep.{u} R G} (i : S.X₃ ⟶ P) (j : P ⟶ Rep.trivial R G R)
    (w : i ≫ j = 0) (hT : (ShortComplex.mk i j w).ShortExact)

/-- The ordinary degree-two class obtained by applying two actual Tate
connecting maps to the invariant scalar one. -/
def scalarDoubleBoundaryClass : groupCohomology S.X₁ 2 :=
  ((TateCohomology.isoGroupCohomology 2).app S.X₁).hom
    (TateCohomology.δ hS 1
      (TateCohomology.δ hT 0 (scalarUnitClass (R := R) (G := G))))

/-- Cup by the double-boundary class is the composite of the two connecting
maps in every integer degree. -/
lemma scalarH2Cup_doubleBoundary
    (sS : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (sT : ((ShortComplex.mk i j w).map
      (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (n : ℤ) (b : tateCohomology (Rep.trivial R G R) n) :
    scalarH2Cup S.X₁ n (scalarDoubleBoundaryClass S hS i j w hT) b =
      tateDeltaTo hS (n + 1) (n + 2) (by omega) (TateCohomology.δ hT n b) := by
  change (tateDegreeIso S.X₁ (add_comm 2 n)).hom
      (cup (scalarPairing S.X₁) 2 n
        (((TateCohomology.isoGroupCohomology 2).app S.X₁).inv
          (((TateCohomology.isoGroupCohomology 2).app S.X₁).hom
            (TateCohomology.δ hS 1
              (TateCohomology.δ hT 0 (scalarUnitClass (R := R) (G := G)))))) b) = _
  rw [Iso.hom_inv_id_apply]
  have hc₁ := scalarCup_delta_first S hS
    (scalarSplit_tensorRight_shortExact S sS _) 1 n
    (TateCohomology.δ hT 0 (scalarUnitClass (R := R) (G := G))) b
  have hc₀ := scalarCup_delta_first (ShortComplex.mk i j w) hT
    (scalarSplit_tensorRight_shortExact _ sT _) 0 n
    (scalarUnitClass (R := R) (G := G)) b
  change cup (scalarPairing S.X₁) 2 n
      (TateCohomology.δ hS 1
        (TateCohomology.δ hT 0 (scalarUnitClass (R := R) (G := G)))) b =
    tateDeltaTo hS (1 + n) (2 + n) (by omega)
      (cup (scalarPairing S.X₃) 1 n
        (TateCohomology.δ hT 0 (scalarUnitClass (R := R) (G := G))) b) at hc₁
  change cup (scalarPairing S.X₃) 1 n
      (TateCohomology.δ hT 0 (scalarUnitClass (R := R) (G := G))) b =
    tateDeltaTo hT (0 + n) (1 + n) (by omega)
      (cup (scalarPairing (Rep.trivial R G R)) 0 n
        (scalarUnitClass (R := R) (G := G)) b) at hc₀
  rw [hc₁, hc₀, scalarCup_unit]
  have houter := ConcreteCategory.congr_hom
    (tateDeltaTo_degreeSquare hS (show 1 + n = n + 1 by omega)
      (show 2 + n = n + 2 by omega) (by omega) (by omega))
    (tateDeltaTo hT (0 + n) (1 + n) (by omega)
      ((tateDegreeIso _ (show n = 0 + n by omega)).hom b))
  change (tateDegreeIso S.X₁ (show 2 + n = n + 2 by omega)).hom
      (tateDeltaTo hS (1 + n) (2 + n) (by omega)
        (tateDeltaTo hT (0 + n) (1 + n) (by omega)
          ((tateDegreeIso _ (show n = 0 + n by omega)).hom b))) =
    tateDeltaTo hS (n + 1) (n + 2) (by omega)
      ((tateDegreeIso S.X₃ (show 1 + n = n + 1 by omega)).hom
        (tateDeltaTo hT (0 + n) (1 + n) (by omega)
          ((tateDegreeIso _ (show n = 0 + n by omega)).hom b))) at houter
  rw [houter]
  congr 1
  have hinner := ConcreteCategory.congr_hom
    (tateDeltaTo_degreeSquare hT (show n = 0 + n by omega)
      (show n + 1 = 1 + n by omega) rfl (by omega)) b
  change (tateDegreeIso S.X₃ (show n + 1 = 1 + n by omega)).hom
      (TateCohomology.δ hT n b) =
    tateDeltaTo hT (0 + n) (1 + n) (by omega)
      ((tateDegreeIso _ (show n = 0 + n by omega)).hom b) at hinner
  rw [← hinner]
  rw [← ModuleCat.comp_apply]
  simp only [tateDegreeIso, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    ModuleCat.id_apply]

/-- If the second middle representation is acyclic and cup by the double
boundary is bijective, then every connecting map of the first row is invertible. -/
lemma scalarDoubleBoundary_delta_isIso
    (sS : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (sT : ((ShortComplex.mk i j w).map
      (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (hP : ∀ n : ℤ, IsZero (tateCohomology P n))
    (hcup : ∀ n : ℤ, Function.Bijective
      (scalarH2Cup S.X₁ n (scalarDoubleBoundaryClass S hS i j w hT)))
    (m : ℤ) : IsIso (TateCohomology.δ hS m) := by
  have hs (n : ℤ) : IsIso (TateCohomology.δ hS (n + 1)) := by
    have hfun :
        (fun b => tateDeltaTo hS (n + 1) (n + 2) (by omega)
          (TateCohomology.δ hT n b)) =
        scalarH2Cup S.X₁ n (scalarDoubleBoundaryClass S hS i j w hT) := by
      funext b
      exact (scalarH2Cup_doubleBoundary S hS i j w hT sS sT n b).symm
    have : IsIso (TateCohomology.δ hT n ≫
        tateDeltaTo hS (n + 1) (n + 2) (by omega)) := by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      change Function.Bijective (fun b =>
        tateDeltaTo hS (n + 1) (n + 2) (by omega) (TateCohomology.δ hT n b))
      rw [hfun]
      exact hcup n
    have := tate_delta_isIso hT n (hP n) (hP (n + 1))
    have hto : IsIso (tateDeltaTo hS (n + 1) (n + 2) (by omega)) :=
      IsIso.of_isIso_comp_left (TateCohomology.δ hT n) _
    change IsIso (TateCohomology.δ hS (n + 1) ≫
      (tateDegreeIso S.X₁ (show n + 1 + 1 = n + 2 by omega)).hom) at hto
    exact IsIso.of_isIso_comp_right (TateCohomology.δ hS (n + 1))
      (tateDegreeIso S.X₁ (show n + 1 + 1 = n + 2 by omega)).hom
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by omega⟩
  exact hs n

/-- The first middle representation is Tate acyclic when the second is acyclic
and the double-boundary class gives bijective cup products in all degrees. -/
lemma scalarDoubleBoundary_middle_isZero
    (sS : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (sT : ((ShortComplex.mk i j w).map
      (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (hP : ∀ n : ℤ, IsZero (tateCohomology P n))
    (hcup : ∀ n : ℤ, Function.Bijective
      (scalarH2Cup S.X₁ n (scalarDoubleBoundaryClass S hS i j w hT)))
    (n : ℤ) : IsZero (tateCohomology S.X₂ n) := by
  have (m : ℤ) : IsIso (TateCohomology.δ hS m) :=
    scalarDoubleBoundary_delta_isIso S hS i j w hT sS sT hP hcup m
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
  exact tate_middle_isZero S hS m inferInstance inferInstance

end TwoRows

end Langlands.Tate
