import Langlands.GroupScheme.FiniteTypeIdentityComponent
import Langlands.GroupScheme.KernelMonomorphism
import Langlands.GroupScheme.Rational.CoordinateSemigroupReduction
import Langlands.GroupScheme.Torus.LinearlyReductiveQuotients
import Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeUnipotentHom
import Langlands.GroupScheme.Torus.NagataFrobeniusImage
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Reduction of connected Nagata necessity by Frobenius images -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a coordinate embedding whose image consists of `p`th powers, one
characteristic-power step lowers the common exponent killing nilpotents. -/
theorem nilpotents_pow_eq_zero_of_injective_of_powers
    {k : Type*} [Field k] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : B →ₐ[k] A) (hφ : Function.Injective φ)
    (p r : ℕ) (hpowers : ∀ a : B, ∃ b : A, φ a = b ^ p)
    (hA : ∀ b : A, IsNilpotent b → b ^ (p ^ (r + 1)) = 0)
    {a : B} (ha : IsNilpotent a) : a ^ (p ^ r) = 0 := by
  obtain ⟨b, hb⟩ := hpowers a
  have hb' : IsNilpotent b := IsNilpotent.of_pow (hb ▸ ha.map φ)
  apply hφ
  rw [map_pow, map_zero, hb, ← pow_mul, ← pow_succ']
  exact hA b hb'

section IdentityComponent

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]

open IdentityComponent.FiniteType in
/-- The induced map on identity components of a flat affine algebraic group
homomorphism is an fppf quotient by its own full kernel. -/
theorem exists_fppfQuotient_identityComponents_of_flat (q : G ⟶ H)
    [Flat q.hom.hom.left] :
    ∃ q₀ : finiteTypeIdentityComponent G ⟶ finiteTypeIdentityComponent H,
      q₀ ≫ finiteTypeIdentityComponentι H = finiteTypeIdentityComponentι G ≫ q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι q₀)) q₀ := by
  let q₀ := factor H (finiteTypeIdentityComponentι G ≫ q)
  have hfac : q₀ ≫ finiteTypeIdentityComponentι H = finiteTypeIdentityComponentι G ≫ q :=
    factor_finiteTypeIdentityComponentι H _
  let : Flat q₀.hom.hom.left :=
    MorphismProperty.of_postcomp (W' := MorphismProperty.monomorphisms _) @Flat
      q₀.hom.hom.left (finiteTypeIdentityComponentι H).hom.hom.left inferInstance (by
        change Flat (q₀ ≫ finiteTypeIdentityComponentι H).hom.hom.left
        rw [hfac]
        exact inferInstanceAs
          (Flat ((finiteTypeIdentityComponentι G).hom.hom.left ≫ q.hom.hom.left)))
  have hsurj := (FiniteTypeIdentityComponent.inclusion_comp_flat_surjective
    (finiteTypeIdentityComponent G) q₀).2
  have hsurj₀ : Surjective q₀.hom.hom.left := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := hsurj.surj y
    exact ⟨(FiniteTypeIdentityComponent.inclusion (finiteTypeIdentityComponent G)).hom.hom.left x,
      hx⟩
  have : LocallyOfFiniteType q₀.hom.hom.left := by
    have : LocallyOfFiniteType (q₀.hom.hom.left ≫ (finiteTypeIdentityComponent H).X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (finiteTypeIdentityComponent H).X.hom
  have : IsLocallyNoetherian (finiteTypeIdentityComponent H).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (finiteTypeIdentityComponent H).X.hom
  exact ⟨q₀, hfac, inferInstance, hsurj₀, inferInstance, rfl⟩

/-- A multiplicative-type kernel and a multiplicative-type target identity
component imply multiplicative type of the source identity component. -/
theorem isMultiplicativeType_identityComponent_of_flat (q : G ⟶ H)
    [Flat q.hom.hom.left] (hK : IsMultiplicativeType (kernel q))
    (hH : IsMultiplicativeType (finiteTypeIdentityComponent H)) :
    IsMultiplicativeType (finiteTypeIdentityComponent G) := by
  obtain ⟨q₀, hfac, hq₀⟩ := exists_fppfQuotient_identityComponents_of_flat q
  have hsub := IsMultiplicativeType.kernel_comp_of_isClosedSubgroup q hK
    (finiteTypeIdentityComponentι G)
    (IdentityComponent.FiniteType.isClosedSubgroup_finiteTypeIdentityComponentι G)
  let : Mono (finiteTypeIdentityComponentι H).hom.hom := Over.mono_of_mono_left _
  have hrange :
      SubgroupFunctor.range (kernelι (finiteTypeIdentityComponentι G ≫ q)) =
        SubgroupFunctor.range (kernelι q₀) := by
    rw [← hfac, range_kernelι_comp_mono]
  let e : kernel q₀ ≅ kernel (finiteTypeIdentityComponentι G ≫ q) :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
      (F := SubgroupFunctor.range (kernelι q₀)) ⟨inferInstance, rfl⟩
      ⟨inferInstance, hrange⟩
  exact (multiplicativeTypeFieldExtension k _ _ _ (kernelι q₀) q₀ inferInstance hq₀).1
    (IsMultiplicativeType.of_iso e hsub) hH (Or.inr inferInstance)

end IdentityComponent

/-- For affine algebraic groups over an algebraically closed field of positive
characteristic, multiplicative type of the identity component reduces to the
reduced case and the first Frobenius kernels of suitable closed embeddings. -/
def NagataConnectedFrobeniusReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [ExpChar k p], 1 < p →
    (∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsReduced G.X.left],
      IsLinearlyReductive G → IsMultiplicativeType (finiteTypeIdentityComponent G)) →
    (∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
      IsLinearlyReductive G →
        ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
          IsClosedSubgroup ρ ∧ IsMultiplicativeType (kernel (ρ.frobeniusPower p 1))) →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
      IsLinearlyReductive G → IsMultiplicativeType (finiteTypeIdentityComponent G)

/-- The connected reduction uses a common nilpotence exponent, with base
case a reduced coordinate algebra and successor case a Frobenius image. -/
theorem nagataConnectedFrobeniusReduction : NagataConnectedFrobeniusReductionStatement.{u} := by
  intro k _ _ p _ hp hred hker
  have byExponent : ∀ (r : ℕ) (G : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
      IsLinearlyReductive G →
      (∀ a : CharacterUnits.Coord G, IsNilpotent a → a ^ (p ^ r) = 0) →
      IsMultiplicativeType (finiteTypeIdentityComponent G) := by
    intro r
    induction r with
    | zero =>
        intro G _ _ hG hnil
        let : _root_.IsReduced (CharacterUnits.Coord G) :=
          ⟨fun a ha => by simpa only [pow_zero, pow_one] using hnil a ha⟩
        let : IsReduced ((algSpec (CommRingCat.of k)).obj (Opposite.op (Lie.coordinateAlgebra G))).left :=
          inferInstanceAs (IsReduced (Spec (CommRingCat.of (CharacterUnits.Coord G))))
        let : IsReduced G.X.left := isReduced_of_isOpenImmersion (Lie.coordinateIso G).inv.left
        exact hred G hG
    | succ r ih =>
        intro G _ _ hG hnil
        obtain ⟨n, ρ, _, hK⟩ := hker G hG
        obtain ⟨I, q, _, hIft, hIa, _, _, hq, hqdom, hqpowers⟩ :=
          frobeniusImageQuotient k p G (Fin n) ρ
        let : LocallyOfFiniteType I.X.hom := hIft
        let : IsAffineHom I.X.hom := hIa
        let : IsSchemeTheoreticallyDominant q.hom.hom.left := hqdom
        let : Flat q.hom.hom.left := hq.1
        have hI := linearlyReductiveSchematicQuotient k G I q hG
        have hImt : IsMultiplicativeType (finiteTypeIdentityComponent I) := ih I hI (fun _ ha =>
          nilpotents_pow_eq_zero_of_injective_of_powers _
            (CoordinateWeights.pullback_injective_of_schemeTheoreticallyDominant q.hom.hom)
            p r hqpowers hnil ha)
        let e : kernel q ≅ kernel (ρ.frobeniusPower p 1) :=
          SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
            (F := SubgroupFunctor.range (kernelι (ρ.frobeniusPower p 1)))
            ⟨inferInstance, hq.2.2.2⟩ ⟨inferInstance, rfl⟩
        exact isMultiplicativeType_identityComponent_of_flat q (IsMultiplicativeType.of_iso e hK) hImt
  intro G _ _ hG
  let A := CharacterUnits.Coord G
  let : IsNoetherianRing A := CoordinateWeights.isNoetherianRing_coord (G := G)
  obtain ⟨r, hr⟩ := IsNoetherianRing.isNilpotent_nilradical A
  refine byExponent r G hG (fun a ha => ?_)
  have hm := Ideal.pow_mem_pow (mem_nilradical.mpr ha) r
  rw [hr] at hm
  exact pow_eq_zero_of_le (Nat.lt_pow_self hp).le (Ideal.mem_bot.mp hm)

end Langlands.GroupScheme
