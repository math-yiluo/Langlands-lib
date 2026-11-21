import Langlands.Geometry.FormalGroup.PDivisibleRationalHom
import Langlands.GroupScheme.AffinePointFaithfullyFlatDescent

/-! # Faithfulness of rationalization for p-divisible groups -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped nonZeroDivisors

namespace Langlands.PDivisibleGroup

open CommGroupScheme

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]
variable {G H : PDivisibleGroup R p}

/-- Evaluation of a natural integer multiple on the actual finite levels. -/
@[simp] theorem Hom.nsmul_app (f : G ⟶ H) (k n : ℕ) : (k • f).app n = k • f.app n :=
  map_nsmul ({ toFun := fun a : G ⟶ H => a.app n
               map_zero' := Hom.zero_app n
               map_add' := fun a b => Hom.add_app a b n } :
    (G ⟶ H) →+ (G.inclusions.obj n ⟶ H.inclusions.obj n)) k f

/-- Multiplying two actual tower morphisms by a p-power is cancellable.
Lift the universal n-th level point into level n+k, compare there using
scalar factorization, and descend the equality faithfully flatly. -/
theorem Hom.pPower_nsmul_injective (k : ℕ) :
    Function.Injective (fun f : G ⟶ H => p ^ k • f) := by
  intro f g h
  apply Hom.ext
  intro n
  let i : n ⟶ n + k := homOfLE (Nat.le_add_right n k)
  let q := G.transfer i
  let j := G.inclusions.map i
  let l := H.inclusions.map i
  have hmul : q ≫ j = p ^ k • (𝟙 (G.inclusions.obj (n + k))) := by
    have hn := G.multiplication i
    rw [Nat.add_sub_cancel_left] at hn
    exact hn
  have he := congrArg (fun a : G ⟶ H => a.app (n + k)) h
  rw [Hom.nsmul_app, Hom.nsmul_app] at he
  have hcomp : q ≫ f.app n ≫ l = q ≫ g.app n ≫ l := by
    calc
      q ≫ f.app n ≫ l = (q ≫ j) ≫ f.app (n + k) := by
        rw [← f.naturality i, Category.assoc]
      _ = p ^ k • f.app (n + k) := by rw [hmul]; simp
      _ = p ^ k • g.app (n + k) := he
      _ = q ≫ g.app n ≫ l := by rw [← g.naturality i, ← Category.assoc, hmul]; simp
  have : IsFinite (G.inclusions.obj n).X.hom := (G.finiteLocallyFree n).1
  have : IsAffine (G.inclusions.obj n).X.left :=
    GroupScheme.Cartier.FiniteDual.isAffine_of_isFinite (G.inclusions.obj n).toGrp
  obtain ⟨C, _, _, ⟨e⟩⟩ := GroupScheme.Cartier.FiniteDual.exists_iso_algSpec (G.inclusions.obj n).X
  let A := CommAlgCat.of R C
  obtain ⟨B, φ, hff, _, y, hy⟩ := (G.shortExact n k).2.2 A e.inv
  let b := (algSpec R).map φ.op
  let f₀ := (f.app n).toMul.hom.hom
  let g₀ := (g.app n).toMul.hom.hom
  have hpoints : (y ≫ q.toMul.hom.hom) ≫ f₀ = (y ≫ q.toMul.hom.hom) ≫ g₀ := by
    apply H.inclusion_affine_injective i B
    have hh := congrArg (fun a : G.inclusions.obj (n + k) ⟶ H.inclusions.obj (n + k) =>
      y ≫ a.toMul.hom.hom) hcomp
    change y ≫ q.toMul.hom.hom ≫ f₀ ≫ l.toMul.hom.hom =
      y ≫ q.toMul.hom.hom ≫ g₀ ≫ l.toMul.hom.hom at hh
    simpa only [Category.assoc] using hh
  change y ≫ q.toMul.hom.hom = b ≫ e.inv at hy
  rw [hy, Category.assoc, Category.assoc] at hpoints
  have hff' := GroupScheme.AffinePointDescent.affinePointMap_injective
    (H.inclusions.obj n).toGrp φ hff
  have hfinal : e.inv ≫ f₀ = e.inv ≫ g₀ := hff' hpoints
  change Additive.ofMul (f.app n).toMul = Additive.ofMul (g.app n).toMul
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  exact (cancel_epi e.inv).1 hfinal

/-- A natural scalar viewed in the p-adic integers acts as its natural multiple. -/
theorem Hom.natCast_smul (k : ℕ) (f : G ⟶ H) : (k : ℤ_[p]) • f = k • f := by
  have h : H.padicAction (k : ℤ_[p]) = (k : End H) := map_natCast H.padicAction k
  rw [smul_eq_comp_padicAction, h, ← nsmul_one]
  change f ≫ (k • (𝟙 H)) = _
  rw [Preadditive.comp_nsmul, Category.comp_id]

/-- The natural map from integral morphisms to the rational tensors is injective. -/
theorem RationalHom.ofHom_injective :
    Function.Injective (RationalHom.ofHom (G := G) (H := H)) := by
  let i := RationalHom.ofHom (G := G) (H := H)
  let : IsLocalizedModule (ℤ_[p])⁰ i := IsLocalization.tensorProduct_isLocalizedModule (ℤ_[p])⁰ ℚ_[p]
  intro f g hfg
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists (ℤ_[p])⁰ i).mp hfg
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero a.property) (PadicInt.irreducible_p (p := p))
  change (a : ℤ_[p]) • f = (a : ℤ_[p]) • g at ha
  rw [he, mul_smul, mul_smul] at ha
  have hn : (p : ℤ_[p]) ^ n • f = (p : ℤ_[p]) ^ n • g := e.isUnit.smul_left_cancel.mp ha
  rw [← Nat.cast_pow, Hom.natCast_smul, Hom.natCast_smul] at hn
  exact Hom.pPower_nsmul_injective n hn

instance : (RationalCategory.inclusion (R := R) (p := p)).Faithful where
  map_injective h := RationalHom.ofHom_injective h

/-- Integral numerators of inverse rational maps compose to the matching
scalar powers on both actual towers. -/
theorem QuasiIsogeny.scalarComposites (e : QuasiIsogeny G H) {n m : ℕ}
    {f : G ⟶ H} {g : H ⟶ G}
    (hf : (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ n • e.hom = RationalHom.ofHom f)
    (hg : (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ m • e.inv = RationalHom.ofHom g) :
    f ≫ g = p ^ (n + m) • (𝟙 G) ∧ g ≫ f = p ^ (m + n) • (𝟙 H) := by
  have hG : RationalHom.comp e.hom e.inv = RationalHom.id G := e.hom_inv_id
  have hH : RationalHom.comp e.inv e.hom = RationalHom.id H := e.inv_hom_id
  constructor
  · apply RationalHom.ofHom_injective
    rw [RationalHom.ofHom_comp, ← hf, ← hg, RationalHom.smul_comp, RationalHom.comp_smul, hG,
      smul_smul, ← pow_add, ← map_pow, IsScalarTower.algebraMap_smul ℚ_[p],
      RationalHom.id, ← map_smul, ← Nat.cast_pow, Hom.natCast_smul]
  · apply RationalHom.ofHom_injective
    rw [RationalHom.ofHom_comp, ← hg, ← hf, RationalHom.smul_comp, RationalHom.comp_smul, hH,
      smul_smul, ← pow_add, ← map_pow, IsScalarTower.algebraMap_smul ℚ_[p],
      RationalHom.id, ← map_smul, ← Nat.cast_pow, Hom.natCast_smul]

namespace QuasiIsogeny

/-- Integral numerators and their clearing exponents for both directions of an isomorphism. -/
structure IntegralPresentation (e : QuasiIsogeny G H) where
  forwardExponent : ℕ
  inverseExponent : ℕ
  numerator : G ⟶ H
  inverseNumerator : H ⟶ G
  clearsHom : (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ forwardExponent • e.hom =
    RationalHom.ofHom numerator
  clearsInv : (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ inverseExponent • e.inv =
    RationalHom.ofHom inverseNumerator

/-- Choose integral numerators of a quasi-isogeny and its inverse. -/
def integralPresentation (e : QuasiIsogeny G H) : IntegralPresentation e := by
  have he : Nonempty (IntegralPresentation e) := by
    obtain ⟨n, f, hf⟩ := RationalHom.exists_pPower_ofHom e.hom
    obtain ⟨m, g, hg⟩ := RationalHom.exists_pPower_ofHom e.inv
    exact ⟨⟨n, m, f, g, hf, hg⟩⟩
  exact Classical.choice he

theorem IntegralPresentation.scalarComposites {e : QuasiIsogeny G H} (P : IntegralPresentation e) :
    P.numerator ≫ P.inverseNumerator = p ^ (P.forwardExponent + P.inverseExponent) • 𝟙 G ∧
      P.inverseNumerator ≫ P.numerator = p ^ (P.inverseExponent + P.forwardExponent) • 𝟙 H :=
  e.scalarComposites P.clearsHom P.clearsInv

end QuasiIsogeny

end Langlands.PDivisibleGroup
