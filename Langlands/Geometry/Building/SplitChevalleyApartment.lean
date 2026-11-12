import Langlands.Geometry.Building.ChevalleyRootFamilyCommutator
import Langlands.Geometry.Building.RootValueTorusNormalizerExtension
import Langlands.Geometry.Building.CrossTorusApartmentData
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.GroupScheme.Reductive.RootDatumWeylProof
import Langlands.GroupScheme.Reductive.SplitIsomorphismProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction
import Langlands.GroupScheme.SplitExistence.Assembly
import Langlands.GroupScheme.SplitExistence.ChevalleyLieExistence
import Langlands.GroupScheme.SplitExistence.ToChevalleyData
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.BruhatTits.Cartan.CentralizerRealComparison

/-! # Normalizer-stable apartment classes of split reductive groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

section Generic

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

namespace RootFunctionFamily

/-- A normalizer point acts on a normalized family by a translation as soon as it
shifts the values on every actual root group by that translation. -/
theorem normalizer_smul_eq_vadd [IsAffineHom G.X.hom]
    (ψ : RootFunctionFamily S G)
    (hroot : ∀ α, α ∉ relativeRoots i → ∀ g, ψ α g = ⊤)
    (hgroup : ∀ α ∈ relativeRoots i, ∀ g, g ∉ rootGroupPoints i α → ψ α g = ⊤)
    (n : normalizerPoints i) (w : V S)
    (hcov : ∀ α ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i α,
      ψ (weylAction i n⁻¹ α) ((n : rationalPoints G)⁻¹ * g * (n : rationalPoints G)) =
        ψ α g + ((eval S α w : ℝ) : WithTop ℝ)) :
    n • ψ = w +ᵥ ψ := by
  apply RootFunctionFamily.ext
  intro α g
  rw [smul_apply, vadd_apply]
  by_cases hα : α ∈ relativeRoots i
  · by_cases hg : g ∈ rootGroupPoints i α
    · exact hcov α hα g hg
    · have hα' : weylAction i n⁻¹ α ∈ relativeRoots i :=
        weylAction_mapsTo_relativeRoots i n⁻¹ hα
      have hg' : (n : rationalPoints G)⁻¹ * g * (n : rationalPoints G) ∉
          rootGroupPoints i (weylAction i n⁻¹ α) := by
        intro hmem
        apply hg
        have he := RelativeRoot.normalizer_conj_mem_iff i α n⁻¹ g
        simp only [constantPoint_self, Subgroup.coe_inv, inv_inv] at he
        exact he.mp hmem
      rw [hgroup _ hα' _ hg', hgroup α hα g hg, WithTop.top_add]
  · have hα' : weylAction i n⁻¹ α ∉ relativeRoots i := by
      intro h
      apply hα
      have h' := weylAction_mapsTo_relativeRoots i n h
      rwa [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        LinearEquiv.coe_one, id] at h'
    rw [hroot _ hα', hroot α hα, WithTop.top_add]

variable (i) in
/-- The normalizer points acting on a family by a translation. -/
def shiftSubgroup (φ : RootFunctionFamily S G) : Subgroup (normalizerPoints i) where
  carrier := {n | ∃ v : V S, n • φ = v +ᵥ φ}
  one_mem' := ⟨0, by rw [one_smul, zero_vadd]⟩
  mul_mem' := by
    rintro n m ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨n • w + v, by rw [mul_smul, hw, smul_vadd, hv, vadd_vadd]⟩
  inv_mem' := by
    rintro n ⟨v, hv⟩
    refine ⟨-(n⁻¹ • v), ?_⟩
    have h : φ = n⁻¹ • v +ᵥ n⁻¹ • φ := by
      rw [← smul_vadd, ← hv, inv_smul_smul]
    calc n⁻¹ • φ = -(n⁻¹ • v) +ᵥ (n⁻¹ • v +ᵥ n⁻¹ • φ) := by
          rw [vadd_vadd, neg_add_cancel, zero_vadd]
      _ = -(n⁻¹ • v) +ᵥ φ := by rw [← h]

theorem mem_shiftSubgroup {φ : RootFunctionFamily S G} {n : normalizerPoints i} :
    n ∈ shiftSubgroup i φ ↔ ∃ v : V S, n • φ = v +ᵥ φ :=
  Iff.rfl

/-- If the translation subgroup contains the centralizer and maps onto the actual
Weyl image, every normalizer point acts by a translation. -/
theorem shiftSubgroup_eq_top [IsAffineHom G.X.hom] (φ : RootFunctionFamily S G)
    (hZ : ∀ z : centralizerPoints i,
      Subgroup.inclusion (centralizerPoints_le_normalizerPoints i) z ∈ shiftSubgroup i φ)
    (hker : (weylAction i).ker = (centralizerPoints i).subgroupOf (normalizerPoints i))
    (hW : weylImage i ≤ (shiftSubgroup i φ).map (weylAction i)) :
    shiftSubgroup i φ = ⊤ := by
  rw [eq_top_iff]
  intro n _
  obtain ⟨h, hh, hhn⟩ := hW ⟨n, rfl⟩
  have hk : h⁻¹ * n ∈ (weylAction i).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hhn, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have hz := hZ ⟨_, hk⟩
  have heq : Subgroup.inclusion (centralizerPoints_le_normalizerPoints i) ⟨_, hk⟩ =
      h⁻¹ * n := Subtype.ext rfl
  rw [heq] at hz
  have := (shiftSubgroup i φ).mul_mem hh hz
  rwa [mul_inv_cancel_left] at this

end RootFunctionFamily

/-- Normalizer-stable apartment data from one compatible valuation whose
normalizer transforms are all translates of it. -/
def KPApartmentData.ofNormalizerShifts [IsAffineHom G.X.hom] (ω : kˣ → ℝ)
    (φ : RootFunctionFamily S G) (hφ : IsRootDatumValuation i φ)
    (hω : IsSplitTorusCompatible i ω φ)
    (hN : ∀ n : normalizerPoints i, ∃ v : V S, n • φ = v +ᵥ φ) :
    KPApartmentData i ω where
  carrier := AddAction.orbit (V S) φ
  exists_eq_orbit := ⟨φ, hφ, hω, rfl⟩
  smul_mem n ψ hψ := by
    obtain ⟨w, rfl⟩ := hψ
    obtain ⟨v, hv⟩ := hN n
    refine ⟨n • w + v, ?_⟩
    change (n • w + v) +ᵥ φ = n • (w +ᵥ φ)
    rw [RootFunctionFamily.smul_vadd, hv, vadd_vadd]

end Generic


namespace ChevalleyRootFamily

open Langlands.GroupScheme.SplitExistence Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  {D : ChevalleyData P b} {k : Type u} [Field k]
  (G : D.ChevGroup k) [Finite J] [P.IsReduced] [Module.Finite ℤ X] [Module.Free ℤ X]
  [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom] [IsAffineHom G.H.X.hom]
  [Mono G.t.hom.hom.left]
  (omega : AddValuation k (WithTop ℝ))

omit [Finite J] [P.IsReduced] [Module.Finite ℤ X] [Module.Free ℤ X] [IsAffine G.H.X.left]
  [LocallyOfFiniteType G.H.X.hom] [IsAffineHom G.H.X.hom] [Mono G.t.hom.hom.left] in
/-- Inverse conjugation by a simple Weyl point on root points. -/
theorem exists_weylPoint_inv_conj_rootPt (i : b.support) (j : J) :
    ∃ ε : ℤˣ, ∀ s : k, (G.weylPoint i)⁻¹ * G.rootPt j s * G.weylPoint i =
      G.rootPt (P.reflectionPerm i j) (((ε : ℤ) : k) * s) := by
  obtain ⟨ε, hε⟩ := G.exists_weylPoint_conj_rootPt i (P.reflectionPerm i j)
  refine ⟨ε, fun s => ?_⟩
  have h := hε (((ε : ℤ) : k) * s)
  rw [RootPairing.reflectionPerm_self] at h
  have hεε : ((ε : ℤ) : k) * (((ε : ℤ) : k) * s) = s := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  rw [hεε] at h
  rw [← h]
  group

/-- The simple Weyl points fix the Chevalley root family. -/
theorem weylNormalizer_smul_family (i : b.support) :
    weylNormalizer G i • family G omega = family G omega := by
  have h := RootFunctionFamily.normalizer_smul_eq_vadd (family G omega)
    (eq_top_of_not_mem_roots G omega) (fun a ha g hg => eq_top_of_not_mem G omega a ha g hg)
    (weylNormalizer G i) 0 ?_
  · rwa [zero_vadd] at h
  intro a ha g hg
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  obtain ⟨s, hs⟩ := (G.rootCoordEquiv j).surjective ⟨g, hg⟩
  have hgs : g = G.rootPt j (Multiplicative.toAdd s) := (congrArg Subtype.val hs).symm
  obtain ⟨ε, hε⟩ := exists_weylPoint_inv_conj_rootPt G i j
  have hW : weylAction G.t (weylNormalizer G i)⁻¹ (charOf k (P.root j)) =
      charOf k (P.root (P.reflectionPerm i j)) := by
    rw [ActsByReflection.inv G (weylNormalizer_actsByReflection G i),
      RootPairing.root_reflectionPerm]
  rw [map_zero, WithTop.coe_zero, add_zero, hW]
  change family G omega _ ((G.weylPoint i)⁻¹ * g * G.weylPoint i) = _
  rw [hgs, hε, family_rootPt, family_rootPt, omega.map_mul, omega_sign, zero_add]

/-- Rational torus points act on the Chevalley root family by translations. -/
theorem centralizer_mem_shiftSubgroup (ω : kˣ → ℝ)
    (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ)) (z : centralizerPoints G.t) :
    Subgroup.inclusion (centralizerPoints_le_normalizerPoints G.t) z ∈
      RootFunctionFamily.shiftSubgroup G.t (family G omega) := by
  obtain ⟨τ, hτ⟩ := exists_eq_of_mem_centralizerPoints G z.property
  have hadd : ∀ x y : kˣ, ω (x * y) = ω x + ω y := by
    intro x y
    have h := omega.map_mul (x : k) (y : k)
    rw [← Units.val_mul, hω, hω, hω, ← WithTop.coe_add, WithTop.coe_eq_coe] at h
    exact h
  have hone : ω 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    linarith
  let f : characterLattice (Tk (X := X) k) →+ ℝ :=
    { toFun := fun a => -ω (rationalCharacterEval
        ((rationalCharacters.equivCharacterLattice _).symm a) τ)
      map_zero' := by
        rw [map_zero, rationalCharacterEval_zero, hone, neg_zero]
      map_add' := by
        intro a c
        rw [map_add, rationalCharacterEval_add, hadd, neg_add] }
  obtain ⟨w, hw⟩ := Langlands.BruhatTits.Cartan.exists_eval_eq (isSplitTorus_Tk k P) f
  refine ⟨w, RootFunctionFamily.centralizer_smul_eq_vadd _ (eq_top_of_not_mem_roots G omega)
    (fun a ha g hg => eq_top_of_not_mem G omega a ha g hg) z w ?_⟩
  intro a ha g hg
  have hc := isSplitTorusCompatible G omega ω hω a ha τ g hg
  rw [rationalPoints.map_apply, hτ] at hc
  rw [hc, hw]
  rfl

omit [Finite J] [P.IsReduced] [Module.Finite ℤ X] [Module.Free ℤ X] [IsAffine G.H.X.left]
  [LocallyOfFiniteType G.H.X.hom] [IsAffineHom G.H.X.hom] in
/-- A normalizer point acting by a reflection also acts by the reflection of the
opposite root. -/
theorem ActsByReflection.reflectionPerm_self {α : J} {m : normalizerPoints G.t}
    (h : ActsByReflection G α m) : ActsByReflection G (P.reflectionPerm α α) m := by
  intro x
  rw [h x]
  congr 1
  rw [RootPairing.reflection_reflectionPerm, ← sq, RootPairing.reflection_sq, one_mul]

/-- Every root and its opposite are realized by reflection elements acting on the
Chevalley root family by translations. -/
theorem exists_shift_actsByReflection (α : J) :
    (∃ m ∈ RootFunctionFamily.shiftSubgroup G.t (family G omega), ActsByReflection G α m) ∧
      ∃ m ∈ RootFunctionFamily.shiftSubgroup G.t (family G omega),
        ActsByReflection G (P.reflectionPerm α α) m := by
  have hsimple : ∀ i : b.support,
      weylNormalizer G i ∈ RootFunctionFamily.shiftSubgroup G.t (family G omega) :=
    fun i => ⟨0, by rw [weylNormalizer_smul_family, zero_vadd]⟩
  refine b.induction_reflect
    (p := fun β => (∃ m ∈ RootFunctionFamily.shiftSubgroup G.t (family G omega),
      ActsByReflection G β m) ∧ ∃ m ∈ RootFunctionFamily.shiftSubgroup G.t (family G omega),
        ActsByReflection G (P.reflectionPerm β β) m) α ?_ ?_ ?_
  · intro β h
    refine ⟨h.2, ?_⟩
    rw [reflectionPerm_neg_self]
    exact h.1
  · intro i hi
    exact ⟨⟨_, hsimple ⟨i, hi⟩, weylNormalizer_actsByReflection G ⟨i, hi⟩⟩,
      ⟨_, hsimple ⟨i, hi⟩,
        (weylNormalizer_actsByReflection G ⟨i, hi⟩).reflectionPerm_self G⟩⟩
  · intro β j h hj
    obtain ⟨⟨m, hm, hmβ⟩, ⟨m', hm', hm'β⟩⟩ := h
    refine ⟨⟨weylNormalizer G ⟨j, hj⟩ * m * (weylNormalizer G ⟨j, hj⟩)⁻¹, ?_,
      hmβ.conj G ⟨j, hj⟩⟩, ⟨weylNormalizer G ⟨j, hj⟩ * m' * (weylNormalizer G ⟨j, hj⟩)⁻¹,
        ?_, ?_⟩⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsimple _) hm)
        (Subgroup.inv_mem _ (hsimple _))
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsimple _) hm')
        (Subgroup.inv_mem _ (hsimple _))
    · have := hm'β.conj G ⟨j, hj⟩
      rwa [reflectionPerm_reflectionPerm_neg] at this

/-- The actual Weyl image is generated by translation-acting reflection elements. -/
theorem weylImage_le_map_shiftSubgroup :
    weylImage G.t ≤
      (RootFunctionFamily.shiftSubgroup G.t (family G omega)).map (weylAction G.t) := by
  have hW := (weylGroup k G.H G.isConnectedReductive (Tk (X := X) k) (isSplitTorus_Tk k P)
    G.t G.isMaximalTorus J (chevDatum k P) G.isRootDatumOf).1
  rw [hW, RootPairing.weylGroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨α, rfl⟩, rfl⟩
  obtain ⟨m, hm, hα⟩ := (exists_shift_actsByReflection G omega α).1
  refine ⟨m, hm, ?_⟩
  apply LinearEquiv.ext
  intro χ
  obtain ⟨x, rfl⟩ := (charEquiv k (X := X)).surjective χ
  rw [RootPairing.Equiv.weightHom_apply, RootPairing.Equiv.reflection_weightEquiv,
    charEquiv_apply, hα x, chevDatum_reflection_charOf]

/-- Every normalizer point acts on the Chevalley root family by a translation. -/
theorem exists_normalizer_smul_family_eq_vadd (ω : kˣ → ℝ)
    (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ)) (n : normalizerPoints G.t) :
    ∃ v : V (Tk (X := X) k), n • family G omega = v +ᵥ family G omega := by
  have hker := (weylGroup k G.H G.isConnectedReductive (Tk (X := X) k) (isSplitTorus_Tk k P)
    G.t G.isMaximalTorus J (chevDatum k P) G.isRootDatumOf).2
  have htop := RootFunctionFamily.shiftSubgroup_eq_top (family G omega)
    (centralizer_mem_shiftSubgroup G omega ω hω) hker (weylImage_le_map_shiftSubgroup G omega)
  have hn : n ∈ RootFunctionFamily.shiftSubgroup G.t (family G omega) := by
    rw [htop]
    exact Subgroup.mem_top n
  exact hn

/-- **The Chevalley apartment.** The equipollence class of the Chevalley root family is
normalizer-stable apartment data. -/
def apartmentData (ω : kˣ → ℝ) (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ))
    (h3 : 3 ≤ (Set.range omega).encard) : KPApartmentData G.t ω :=
  KPApartmentData.ofNormalizerShifts ω (family G omega) (isRootDatumValuation G omega h3)
    (isSplitTorusCompatible G omega ω hω) (exists_normalizer_smul_family_eq_vadd G omega ω hω)

end ChevalleyRootFamily

section Split

variable {k : Type u} [Field k]

open Langlands.GroupScheme.SplitExistence Langlands.GroupScheme.SplitExistence.ChevalleyData

/-- **Normalizer-stable apartments of split groups** (Kaletha–Prasad §6.1(a)). Let `j` be a
split maximal torus of a connected reductive group `G` over a field, and let `omega` be an
additive valuation of the field with at least three values, agreeing with `ω` on units. Then
there is normalizer-stable apartment data for `j` and `ω`: the transport of the class of the
Chevalley root family of a Chevalley group with the same root datum. -/
theorem nonempty_kpApartmentData_of_isSplitTorus (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) [Mono j.hom.hom.left] (hj : IsMaximalTorus j)
    (omega : AddValuation k (WithTop ℝ)) (ω : kˣ → ℝ)
    (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ))
    (h3 : 3 ≤ (Set.range omega).encard) : Nonempty (KPApartmentData j ω) := by
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence k G hG T hT j hj
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  have := isTorsionFree_weight P
  obtain ⟨b⟩ := nonempty_base_int P
  obtain ⟨DL⟩ := nonempty_chevalleyLieData P b
  let D : ChevalleyData P b := DL.toChevalleyData
  obtain ⟨Gc⟩ := D.nonempty_chevGroup k
  have : IsAffineHom Gc.H.X.hom := Gc.affine
  have : IsAffine Gc.H.X.left := isAffine_of_isAffineHom Gc.H.X.hom
  have : Smooth Gc.H.X.hom := Gc.smooth
  have hGcmax : IsMaximalTorus Gc.t := Gc.isMaximalTorus
  have : IsClosedImmersion Gc.t.hom.hom.left := hGcmax.2.1
  let Dc := ChevalleyRootFamily.apartmentData Gc omega ω hω h3
  let t : T ≅ Tk (X := characterLattice T) k :=
    hT.isoOfCharacterEquiv (isSplitTorus_Tk k P) (charEquiv k (X := characterLattice T))
  have hR : IsRootDatumOf (CommGroupScheme.groupHom t.hom ≫ Gc.t) P :=
    IsRootDatumOf.precomp_torusIso t Gc.isRootDatumOf hP.1 (chevDatumEquiv k P) fun χ => by
      rw [hT.character_congr_isoOfCharacterEquiv (isSplitTorus_Tk k P)]
      rfl
  have hM : IsMaximalTorus (CommGroupScheme.groupHom t.hom ≫ Gc.t) :=
    IsMaximalTorus.precomp_torusIso t hGcmax
  obtain ⟨ψ, hψ⟩ := splitCommonTorusIsomorphism k G Gc.H hG Gc.isConnectedReductive T hT j
    (CommGroupScheme.groupHom t.hom ≫ Gc.t) hj hM J J P P hP hR (Equiv.refl J) rfl rfl
  exact ⟨Dc.transport t.symm ψ.symm (torusTransport_inverse_square t ψ hψ)⟩

/-- **The split apartment.** A chosen normalizer-stable apartment class for a split maximal
torus of a connected reductive group, from `nonempty_kpApartmentData_of_isSplitTorus`. -/
def KPApartmentData.ofSplitMaximalTorus (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) [Mono j.hom.hom.left] (hj : IsMaximalTorus j)
    (omega : AddValuation k (WithTop ℝ)) (ω : kˣ → ℝ)
    (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ))
    (h3 : 3 ≤ (Set.range omega).encard) : KPApartmentData j ω :=
  Classical.choice (nonempty_kpApartmentData_of_isSplitTorus G hG T hT j hj omega ω hω h3)

end Split

end Langlands.Geometry.Building
