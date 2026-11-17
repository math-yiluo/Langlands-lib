import Langlands.GroupScheme.Reductive.AffineSplitIsogenyWordData
import Langlands.GroupScheme.Reductive.B2PowerCommutatorTransport
import Langlands.LinearAlgebra.RootDatumIsogenyRankTwo
import Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity

/-! # The exceptional B2 relations for actual powered Weyl families -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {H : GroupScheme (Spec (CommRingCat.of R))}
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)

/-- The root power has the actual scalar-point formula on every scheme test. -/
theorem rootPoint_rootPower (j' : J') (Z : Over (Spec (CommRingCat.of R)))
    (x : Γ(Z.left, ⊤)) :
    rootPoint (rootPower f hchar j') Z x =
      VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ f.rootFactor j') := by
  rw [rootPoint, rootPower_hom, AdditiveLinePower.scalarPoint_comp_powerMap]

/-- Word conjugation of a powered arbitrary map commutes with its additive power. -/
theorem wordConj_rootMap (u' : J' → (Ga R ⟶ H)) (l : List J) (j' : J')
    (w : Ga R ⟶ H) :
    wordConj P (poweredRootFamily f hchar u') l (rootMap f hchar j' w) =
      rootMap f hchar j' (wordConj Q u' (l.map f.indexEquiv.symm) w) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change wordConj P (poweredRootFamily f hchar u') l (rootMap f hchar j' w) ≫
        (H.innerIso (rootWeylPoint P (poweredRootFamily f hchar u') a)).hom = _
    rw [ih, rootWeylPoint_poweredRootFamily]
    exact Category.assoc _ _ _

variable {b : P.Base} {b' : Q.Base}

/-- Powering the source Weyl family equals the prescribed power of the corresponding
target Weyl family for the transported words. -/
theorem weylFamily_powered_eq
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H)) (α : J) :
    weylFamily P W (poweredRootFamily f hchar u') α =
      rootMap f hchar (f.indexEquiv.symm α)
        (weylFamily Q (targetSimpleWords f hb W) u' (f.indexEquiv.symm α)) := by
  rw [weylFamily_poweredRootFamily, targetWordFamily_eq_weylFamily f hb W u']
  rfl

/-- The same identity holds after any additional word conjugation. -/
theorem wordConj_weylFamily_powered_eq
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H)) (l : List J) (α : J) :
    wordConj P (poweredRootFamily f hchar u') l
        (weylFamily P W (poweredRootFamily f hchar u') α) =
      rootMap f hchar (f.indexEquiv.symm α)
        (wordConj Q u' (l.map f.indexEquiv.symm)
          (weylFamily Q (targetSimpleWords f hb W) u' (f.indexEquiv.symm α))) := by
  rw [weylFamily_powered_eq f hchar hb W u', wordConj_rootMap]

/-- The two standard source B2 word relations for the actual powered maps. -/
def PoweredB2WordRelations (W : ∀ α, SimpleWord P b α)
    (u' : J' → (Ga R ⟶ H)) (a c : J) : Prop :=
  let v := poweredRootFamily f hchar u'
  let w := weylFamily P W v
  CommRel (w a) (w c)
      (wordTerms (P := P) v w [([c], a, 1, 1, 1), ([a], c, 1, 2, 1)]) ∧
    CommRel (w a) (wordConj P v [c] (w a))
      (wordTerms (P := P) v w [([a], c, 2, 1, 1)])

section NormalTarget

variable [IsLocalRing R] [DecidableEq I'] [IsAffineHom H.X.hom]
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}

/-- A genuine normalized target B2 pair with exchanged lengths satisfies the two source
B2 relations after the powers prescribed by the root-datum isogeny. -/
theorem poweredB2WordRelations_of_normalData
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
    (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')
    {a c : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (hP : P.pairingIn ℤ a c = -1)
    (hQ₁ : Q.pairingIn ℤ (f.indexEquiv.symm c) (f.indexEquiv.symm a) = -1)
    (hQ₂ : Q.pairingIn ℤ (f.indexEquiv.symm a) (f.indexEquiv.symm c) = -2) :
    PoweredB2WordRelations f hchar W u' a c := by
  classical
  let A := f.indexEquiv.symm a
  let C := f.indexEquiv.symm c
  let w := weylFamily Q (targetSimpleWords f hb W) u'
  have hA := hb a ha
  have hC := hb c hc
  have hCA : C ≠ A := fun h => hac (f.indexEquiv.symm.injective h.symm)
  have hratio : f.rootFactor A = 2 * f.rootFactor C := by
    change f.rootFactor (f.indexEquiv.symm a) = 2 * f.rootFactor (f.indexEquiv.symm c)
    have h := f.rootFactor_mul_pairingIn A C
    simp only [A, C, Equiv.apply_symm_apply, hP, hQ₂] at h
    omega
  have hp : p = 2 :=
    f.characteristicExponent_eq_of_rootFactor_ratio Nat.prime_two C A hratio
  have h₂ : (2 : R) = 0 := by
    have hq := f.rootFactor_pos C
    have hne : f.rootFactor A ≠ 1 := by omega
    simpa only [hp, Nat.cast_ofNat] using hchar A hne
  have hFq := rootPoint_rootPower f hchar C
  have hF2q : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint (rootPower f hchar A) Z x =
        VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ (2 * f.rootFactor C)) := by
    intro Z x
    rw [rootPoint_rootPower, hratio]
  obtain ⟨hprincipal, _⟩ := hd.b2_commRels hC hA hCA hQ₁ hQ₂
  have hraw := b2_unequal_power_commRel (w A) (w C)
    (wordConj Q u' [A] (w C)) (wordConj Q u' [C] (w A))
    hprincipal h₂ (rootPower f hchar C) (rootPower f hchar A) (f.rootFactor C)
    hFq hF2q
  have hli : LinearIndependent ℤ ![Q.root C, Q.root A] :=
    b'.linearIndependent_pair_of_ne (i := ⟨C, hC⟩) (j := ⟨A, hA⟩)
      (fun h => hCA (congrArg Subtype.val h))
  have hroots := b2_roots hQ₁ hQ₂
  have hx : Q.root A = (0 : ℤ) • Q.root C + (1 : ℤ) • Q.root A := by simp
  have hy : Q.root (Q.reflectionPerm C A) =
      (2 : ℤ) • Q.root C + (1 : ℤ) • Q.root A := by simpa using hroots.2
  have hcone := noOpp_cone_of_coeffs hli hx hy
    (fun α m n h => Langlands.LinearAlgebra.b2_coeffs hC hA hCA hQ₁ hQ₂ h)
    (by norm_num) (by intro s t hs ht h; omega)
  have hcomm := hd.pointsCommute hcone.1 hcone.2
  have hparam : IsRootParametrization i' (Q.root (Q.reflectionPerm C A))
      (wordConj Q u' [C] (w A)) := by
    have h := isRootParametrization_wordConj (P := Q) (u := u') [C]
      (fun j hj => by
        obtain rfl := List.mem_singleton.mp hj
        exact hd.weyl C hC)
      (hd.isRootParametrization A)
    simpa only [wordReflect, List.foldr_cons, List.foldr_nil,
      RootPairing.root_reflectionPerm] using h
  obtain ⟨κ, hκ, _⟩ := hparam.existsUnique_unit_of_rootDatum hd.rootDatum
    (Q.reflectionPerm C A) (hd.isRootParametrization (Q.reflectionPerm C A))
  have hAW : PointsCommute (w A) (wordConj Q u' [C] (w A)) :=
    hcomm.of_scaleHom 1 (κ : R)
      (by rw [scaleHom_one, Category.id_comp]) hκ
  have hmixed := b2_mixed_unequal_power_commRel (w A)
    (wordConj Q u' [A] (w C)) (wordConj Q u' [C] (w A))
    hAW h₂ (rootPower f hchar C) (rootPower f hchar A) (f.rootFactor C) hF2q
  constructor
  · simp only [wordTerms, List.map_cons, List.map_nil,
      weylFamily_powered_eq f hchar hb W u', wordConj_rootMap]
    exact hraw
  · simp only [wordTerms, List.map_cons, List.map_nil,
      weylFamily_powered_eq f hchar hb W u', wordConj_rootMap]
    exact hmixed

end NormalTarget

end Langlands.GroupScheme.AffineRootDatumIsogeny
