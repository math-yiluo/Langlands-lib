import Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeMinimalParabolicLevi
import Langlands.GroupScheme.Rational.QuadraticOppositeBorelExistence
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.GroupScheme.Rational.LeviPreimageSolvableRadical
import Langlands.GroupScheme.Rational.LeviAmbientTransport
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Descent.GaloisClosedSubgroups
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Existence of a quadratic opposite minimal parabolic and its Levi subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

private theorem basePoint_smul_inf' {S : Scheme.{u}} {G : GroupScheme S}
    (g : Over.mk (𝟙 S) ⟶ G.X) (A B : SubgroupFunctor G) :
    g • (A ⊓ B) = (g • A) ⊓ (g • B) := by
  apply SubgroupFunctor.ext
  intro Z
  apply Subgroup.ext
  intro z
  simp only [SubgroupFunctor.inf_carrier, Subgroup.mem_inf, SubgroupFunctor.mem_basePoint_smul]

/-- Precomposing a rational Levi with an isomorphism of group schemes gives a rational Levi,
with the same unipotent radical. -/
private theorem isRationalLeviSubgroup_iso_comp {k : Type u} [Field k]
    {L L' P : GroupScheme (Spec (CommRingCat.of k))} {l : L ⟶ P}
    (hl : IsRationalLeviSubgroup l) (e : L' ≅ L) : IsRationalLeviSubgroup (e.hom ≫ l) := by
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  have hm : subgroupMultiplication (e.hom ≫ l) r =
      (e.hom.hom.hom ▷ U.X) ≫ subgroupMultiplication l r := by
    simp only [subgroupMultiplication, Grp.comp_hom_hom, MonObj.comp_mul,
      CartesianMonoidalCategory.whiskerRight_fst_assoc,
      CartesianMonoidalCategory.whiskerRight_snd_assoc]
  have : IsIso e.hom.hom.hom := (inferInstance : IsIso ((Grp.forget _).mapIso e).hom)
  have : IsIso (subgroupMultiplication l r) := hmul
  refine ⟨hl.isAffineHom, IsClosedSubgroup.iso_comp e hl.isClosedSubgroup,
    IsConnectedReductive.of_iso e hl.isConnectedReductive, U, r, hr, ?_⟩
  rw [hm]
  infer_instance

section Transport

variable {F Q : Type u} [Field F] [Field Q] [Algebra F Q]
  {G : GroupScheme (Spec (CommRingCat.of F))}

local notation "b" => algebraBaseMap F Q
local notation "GQ" => Functor.obj (GroupScheme.baseChange b) G

omit [Algebra F Q] in
/-- The Galois translate of a closed subgroup is a closed subgroup. -/
theorem isClosedSubgroup_radicalGaloisHom [Algebra F Q]
    {P : GroupScheme (Spec (CommRingCat.of Q))} {j : P ⟶ GQ}
    (hj : IsClosedSubgroup j) (σ : Q ≃ₐ[F] Q) :
    IsClosedSubgroup (radicalGaloisHom j σ) :=
  (hj.baseChange (galoisBaseMap F Q σ)).comp_iso _

/-- The Galois translate of a parabolic subgroup is a parabolic subgroup: both are dynamic
parabolics, of a cocharacter and of its Galois transport. -/
theorem isParabolicSubgroup_radicalGaloisHom (hGQ : IsConnectedReductive GQ)
    {P : GroupScheme (Spec (CommRingCat.of Q))} {j : P ⟶ GQ}
    (hj : IsParabolicSubgroup j) (σ : Q ≃ₐ[F] Q) :
    IsParabolicSubgroup (radicalGaloisHom j σ) := by
  have hjc := hj.isClosedSubgroup
  obtain ⟨χ, hχ⟩ := (parabolicDynamic Q GQ hGQ P j hjc).1 hj
  refine (parabolicDynamic Q GQ hGQ _ _ (isClosedSubgroup_radicalGaloisHom hjc σ)).2
    ⟨transportCocharacter b (galoisBaseMap F Q σ) (galoisBaseMap_over F Q σ) G χ, ?_⟩
  rw [Dynamic.parabolic_transportCocharacter_eq_descentTransport, ← hχ,
    SubgroupFunctor.descentTransport_range]
  rfl

/-- The Galois translate of a minimal parabolic subgroup is a minimal parabolic subgroup. -/
theorem isMinimalParabolicSubgroup_radicalGaloisHom (hGQ : IsConnectedReductive GQ)
    {P : GroupScheme (Spec (CommRingCat.of Q))} {j : P ⟶ GQ}
    (hj : IsMinimalParabolicSubgroup j) (σ : Q ≃ₐ[F] Q) :
    IsMinimalParabolicSubgroup (radicalGaloisHom j σ) := by
  let ρ := SubgroupFunctor.galoisTransport F Q G
  have htr {H : GroupScheme (Spec (CommRingCat.of Q))} (i : H ⟶ GQ) (τ : Q ≃ₐ[F] Q) :
      ρ τ (SubgroupFunctor.range i) = SubgroupFunctor.range (radicalGaloisHom i τ) :=
    SubgroupFunctor.descentTransport_range _ _ _ _ i
  have hinv (τ τ' : Q ≃ₐ[F] Q) (hττ : τ * τ' = 1) (D : SubgroupFunctor GQ) :
      ρ τ (ρ τ' D) = D := by
    change (ρ τ * ρ τ') D = D
    rw [← map_mul, hττ, map_one]
    rfl
  have hmono (τ : Q ≃ₐ[F] Q) {D D' : SubgroupFunctor GQ} (h : D ≤ D') : ρ τ D ≤ ρ τ D' := by
    intro Z z hz
    change z ∈ (SubgroupFunctor.descentTransport _ _ _ _ D).carrier Z at hz
    change z ∈ (SubgroupFunctor.descentTransport _ _ _ _ D').carrier Z
    rw [SubgroupFunctor.mem_descentTransport_iff_descentPoint] at hz ⊢
    exact h _ hz
  refine ⟨isParabolicSubgroup_radicalGaloisHom hGQ hj.1 σ, fun Q' j' hj' hle => ?_⟩
  have h₁ : SubgroupFunctor.range (radicalGaloisHom j' σ⁻¹) = SubgroupFunctor.range j := by
    apply hj.2 _ _ (isParabolicSubgroup_radicalGaloisHom hGQ hj' σ⁻¹)
    rw [← htr, ← hinv σ⁻¹ σ (inv_mul_cancel σ) (SubgroupFunctor.range j)]
    apply hmono σ⁻¹
    rw [htr]
    exact hle
  calc SubgroupFunctor.range j' = ρ σ (ρ σ⁻¹ (SubgroupFunctor.range j')) :=
        (hinv σ σ⁻¹ (mul_inv_cancel σ) _).symm
    _ = ρ σ (SubgroupFunctor.range j) := by rw [htr j' σ⁻¹, h₁]
    _ = SubgroupFunctor.range (radicalGaloisHom j σ) := htr j σ

end Transport

section Descent

variable {F Q : Type u} [Field F] [Field Q] [Algebra F Q]
  [FiniteDimensional F Q] [IsGalois F Q]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local notation "b" => algebraBaseMap F Q
local notation "GQ" => Functor.obj (GroupScheme.baseChange b) G

omit [FiniteDimensional F Q] [IsGalois F Q] [IsAffineHom G.X.hom] in
private theorem transport_inf' (σ : Q ≃ₐ[F] Q) (A B : SubgroupFunctor GQ) :
    SubgroupFunctor.galoisTransport F Q G σ (A ⊓ B) =
      SubgroupFunctor.galoisTransport F Q G σ A ⊓
        SubgroupFunctor.galoisTransport F Q G σ B := by
  apply SubgroupFunctor.ext
  intro Z
  apply Subgroup.ext
  intro z
  change z ∈ (SubgroupFunctor.descentTransport _ _ _ _ (A ⊓ B)).carrier Z ↔
    z ∈ (SubgroupFunctor.descentTransport _ _ _ _ A ⊓
      SubgroupFunctor.descentTransport _ _ _ _ B).carrier Z
  rw [SubgroupFunctor.mem_descentTransport_iff_descentPoint, SubgroupFunctor.inf_carrier,
    Subgroup.mem_inf, SubgroupFunctor.inf_carrier, Subgroup.mem_inf,
    SubgroupFunctor.mem_descentTransport_iff_descentPoint,
    SubgroupFunctor.mem_descentTransport_iff_descentPoint]

/-- A rational Levi subgroup of a minimal parabolic subgroup `P` of `G_Q` that is the full
intersection of `P` with its Galois translate descends to a closed subgroup of `G` over `F`
satisfying `IsQuadraticOppositeMinimalParabolicLevi`. -/
theorem exists_quadraticOppositeMinimalParabolicLevi_of_intersection
    (hdeg : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q) (hσ : σ ≠ 1)
    {P L : GroupScheme (Spec (CommRingCat.of Q))} (j : P ⟶ GQ) (l : L ⟶ P)
    (hj : IsMinimalParabolicSubgroup j) (hl : IsRationalLeviSubgroup l)
    (hinter : SubgroupFunctor.range j ⊓ SubgroupFunctor.range (radicalGaloisHom j σ) =
      SubgroupFunctor.range (l ≫ j)) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of F))) (t : C ⟶ G),
      IsQuadraticOppositeMinimalParabolicLevi Q t := by
  classical
  let ρ := SubgroupFunctor.galoisTransport F Q G
  let tQ := l ≫ j
  have htQ : IsClosedSubgroup tQ := hl.isClosedSubgroup.comp hj.1.isClosedSubgroup
  have hcard : Nat.card (Q ≃ₐ[F] Q) = 2 := (IsGalois.card_aut_eq_finrank F Q).trans hdeg
  have hσ₂ : σ ^ 2 = 1 := by simpa only [hcard] using (pow_card_eq_one' (x := σ))
  obtain ⟨_, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : Q ≃ₐ[F] Q)).mp hcard
  have htransport {H : GroupScheme (Spec (CommRingCat.of Q))} (i : H ⟶ GQ)
      (τ : Q ≃ₐ[F] Q) : ρ τ (SubgroupFunctor.range i) =
        SubgroupFunctor.range (radicalGaloisHom i τ) :=
    SubgroupFunctor.descentTransport_range _ _ _ _ i
  have hinv (τ : Q ≃ₐ[F] Q) :
      SubgroupFunctor.range (radicalGaloisHom tQ τ) = SubgroupFunctor.range tQ := by
    rw [← htransport, ← hinter]
    by_cases ht : τ = 1
    · subst τ
      exact congrFun (map_one ρ) _
    have ht' : τ = σ := (huniq τ ht).trans (huniq σ hσ).symm
    subst τ
    simp only [← htransport]
    change ρ σ (_ ⊓ _) = _
    rw [show ρ σ (_ ⊓ _) = _ from transport_inf' σ _ _]
    have htwice (D : SubgroupFunctor GQ) : ρ σ (ρ σ D) = D := by
      change (ρ σ * ρ σ) D = D
      rw [← map_mul, ← pow_two, hσ₂, map_one]
      rfl
    rw [htwice]
    apply SubgroupFunctor.ext
    intro Z
    simp only [SubgroupFunctor.inf_carrier]
    exact inf_comm _ _
  obtain ⟨C, t, e, _, ht, he⟩ := htQ.exists_descent_of_galois_range_eq hinv
  refine ⟨C, t, hdeg, ht, σ, P, j, e.hom ≫ l, hσ, hj, isRationalLeviSubgroup_iso_comp hl e,
    ?_, ?_⟩
  · rw [Category.assoc]
    exact he.symm
  · rw [hinter, he, SubgroupFunctor.range_iso_comp]

end Descent

section Existence

variable {F Q : Type u} [Field F] [Infinite F] [Field Q] [Algebra F Q]
  [FiniteDimensional F Q] [IsGalois F Q]
  {G : GroupScheme (Spec (CommRingCat.of F))}

local notation "b" => algebraBaseMap F Q
local notation "GQ" => Functor.obj (GroupScheme.baseChange b) G

/-- Platonov–Rapinchuk, Lemma 6.17', for the class of minimal parabolic subgroups: a connected
reductive group over an infinite field has, over a quadratic Galois extension `Q`, a minimal
parabolic subgroup `P` of `G_Q` whose intersection with its Galois translate is a rational
Levi subgroup of `P` descending to the ground field. -/
theorem exists_quadraticOppositeMinimalParabolicLevi
    (hdeg : Module.finrank F Q = 2) (hG : IsConnectedReductive G) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of F))) (t : C ⟶ G),
      IsQuadraticOppositeMinimalParabolicLevi Q t := by
  classical
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hGQ : IsConnectedReductive GQ := connectedReductiveFieldExtensionStatement F Q G hG
  let : Smooth (GQ).X.hom := hGQ.smooth
  let : IsAffineHom (GQ).X.hom := hGQ.isAffineHom
  let : IsAffine (GQ).X.left := isAffine_of_isAffineHom (GQ).X.hom
  have hcard : Nat.card (Q ≃ₐ[F] Q) = 2 := (IsGalois.card_aut_eq_finrank F Q).trans hdeg
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : Q ≃ₐ[F] Q)).mp hcard
  obtain ⟨S, i, hi⟩ := exists_maximalSplitTorus GQ
  obtain ⟨ν, hν⟩ := hi.1.1.exists_genericCocharacter i
  have hν' : IsGenericCocharacter i (-ν) := fun a ha => by
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χ' := Dynamic.oppositeCocharacter χ
  have hmin : IsMinimalParabolicFunctor (Dynamic.parabolic χ) :=
    genericMinimalParabolic Q GQ hGQ S i hi ν hν
  have hmin' : IsMinimalParabolicFunctor (Dynamic.parabolic χ') := by
    have h := genericMinimalParabolic Q GQ hGQ S i hi (-ν) hν'
    rwa [groupHom_neg_comp_eq_oppositeCocharacter] at h
  obtain ⟨B, j, hj, hjP⟩ := isMinimalParabolicFunctor_iff_exists.mp hmin
  obtain ⟨B', p₁, hp₁, hp₁P⟩ := isMinimalParabolicFunctor_iff_exists.mp hmin'
  let : IsClosedImmersion j.hom.hom.left := hj.1.isClosedSubgroup
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hjP⟩
  have hZ := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hUχ := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let l := hP.factorHom (Dynamic.Affine.centralizerHom χ)
    (by rw [hZ.2]; exact Dynamic.centralizer_le_parabolic χ)
  let r := hP.factorHom (Dynamic.Affine.unipotentHom χ)
    (by rw [hUχ.2]; exact Dynamic.unipotent_le_parabolic χ)
  have hl : l ≫ j = Dynamic.Affine.centralizerHom χ := hP.factorHom_comp _ _
  have hr : r ≫ j = Dynamic.Affine.unipotentHom χ := hP.factorHom_comp _ _
  have hZred := dynamicCentralizerReductive Q GQ hGQ χ _ (Dynamic.Affine.centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ) hZ
  have hrad := Dynamic.isGeometricUnipotentRadical_of_centralizer χ
    (Dynamic.Affine.centralizerHom χ) j r hP (by rw [hr]; exact hUχ) hZ hZred
  have hlevi : IsRationalLeviSubgroup l :=
    Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical hP hZ hUχ l r hl hr hZred hrad
  let jσ := radicalGaloisHom j σ
  have hjσ : IsMinimalParabolicSubgroup jσ := isMinimalParabolicSubgroup_radicalGaloisHom hGQ hj σ
  obtain ⟨w, E, hw'⟩ := minimalParabolicConjugacy Q GQ hGQ _ _ jσ p₁ hjσ hp₁
  let U := Dynamic.Affine.unipotentScheme χ
  let u := Dynamic.Affine.unipotentHom χ
  let PP := Dynamic.Affine.parabolicScheme χ'
  let p := Dynamic.Affine.parabolicHom χ'
  have hp' := Dynamic.Affine.isRepresentedBy_parabolicHom χ'
  have hw : w • SubgroupFunctor.range jσ = SubgroupFunctor.range p := by
    rw [SubgroupFunctor.basePoint_smul_range, hw', SubgroupFunctor.range_iso_comp, hp₁P, hp'.2]
  let m := SubgroupFunctor.cellMultiplication u p
  have hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ')).IsRepresentedBy u := by
    simpa only [χ', Dynamic.oppositeCocharacter_oppositeCocharacter] using
      Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let : IsOpenImmersion m.left := oppositeCellStatement Q GQ χ' U PP u p hU hp'
  let R := (GQ).rightTranslationIso w
  let mW := m ≫ R.hom
  let : IsIso R.hom.left := (Over.forget _).map_isIso R.hom
  let : IsOpenImmersion mW.left := inferInstanceAs (IsOpenImmersion (m.left ≫ R.hom.left))
  have hW : IsOpen (Set.range mW.left) := IsOpenImmersion.isOpen_range mW.left
  have hnW : (Set.range mW.left).Nonempty := by
    let z : (Over.mk (𝟙 (Spec (CommRingCat.of Q)))) ⟶ U.X ⊗ PP.X :=
      CartesianMonoidalCategory.lift 1 1
    exact ⟨_, z.left (IsLocalRing.closedPoint Q), rfl⟩
  have hd := galoisTwistedPointDensity_of_isGalois F Q G hG σ hσ 1
  obtain ⟨x, hx, hxD⟩ := hd.inter_open_nonempty _ hW hnW
  obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp hxD
  let e := GaloisPointComparison.baseChangeCoeffEquiv F Q G
  let g := e.symm a
  let a₀ : G.affinePoints (CommAlgCat.of F Q) := a
  let aσ : G.affinePoints (CommAlgCat.of F Q) := GaloisPoint.conjugate F Q G σ a₀
  let z := e.symm (a₀⁻¹ * 1 * aσ)
  have hy' : z.left y = x := hy
  have hzW : Set.range z.left ⊆ Set.range mW.left := by
    rintro _ ⟨y', rfl⟩
    have : Subsingleton ↥(Over.mk (𝟙 (Spec (CommRingCat.of Q)))).left :=
      inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of Q)))
    rw [show y' = y from Subsingleton.elim _ _, hy']
    exact hx
  have hcell : Set.range (z ≫ R.inv).left ⊆ Set.range m.left := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨v, hv⟩ := hzW ⟨s, rfl⟩
    refine ⟨v, ?_⟩
    change m.left v = R.inv.left (z.left s)
    rw [← hv]
    change m.left v = (m ≫ R.hom ≫ R.inv).left v
    rw [R.hom_inv_id, Category.comp_id]
  obtain ⟨v, v', hfactor⟩ := SubgroupFunctor.exists_cell_factors_of_range_subset u p
    (z ≫ R.inv) hcell
  let q := v ≫ u.hom.hom
  let q' := v' ≫ p.hom.hom
  have hz : z = q * q' * w := by
    have hr := congrArg (fun f => f ≫ R.hom) hfactor
    rw [Category.assoc, R.inv_hom_id, Category.comp_id] at hr
    change z = (q * q') ≫ (GQ).rightTranslation w at hr
    rwa [comp_rightTranslation, constantPoint_self] at hr
  have hgσ : GaloisPointComparison.rationalConjugate F Q G σ g = g * z := by
    apply e.injective
    have ha : e g = a₀ := e.apply_symm_apply a₀
    have hz' : e z = a₀⁻¹ * 1 * aσ := e.apply_symm_apply _
    rw [GaloisPointComparison.baseChangeCoeffEquiv_rationalConjugate, map_mul, ha, hz',
      mul_one, mul_inv_cancel_left]
  have hqmem : q ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of Q)))) := by
    have hu : q ∈ (SubgroupFunctor.range u).carrier (Over.mk (𝟙 (Spec (CommRingCat.of Q)))) :=
      SubgroupFunctor.mem_range.mpr ⟨v, rfl⟩
    rw [(Dynamic.Affine.isRepresentedBy_unipotentHom χ).2] at hu
    have hq := Dynamic.unipotent_le_parabolic χ _ hu
    rwa [← hP.2] at hq
  obtain ⟨s, hs⟩ := SubgroupFunctor.mem_range.mp hqmem
  have hq : q • SubgroupFunctor.range j = SubgroupFunctor.range j := by
    rw [← hs, SubgroupFunctor.basePoint_smul_range, range_comp_innerIso_of_mem]
  have hq' : q' • SubgroupFunctor.range p = SubgroupFunctor.range p := by
    dsimp only [q']
    rw [SubgroupFunctor.basePoint_smul_range, range_comp_innerIso_of_mem]
  have hop : SubgroupFunctor.range j ⊓ SubgroupFunctor.range p =
      SubgroupFunctor.range (Dynamic.Affine.centralizerHom χ) := by
    rw [hP.2, hp'.2, Dynamic.parabolic_inf_opposite_eq_centralizer, hZ.2]
  let j' := j ≫ ((GQ).innerIso g).hom
  let t' := Dynamic.Affine.centralizerHom χ ≫ ((GQ).innerIso (g * q)).hom
  have hinter : SubgroupFunctor.range j' ⊓ SubgroupFunctor.range (radicalGaloisHom j' σ) =
      SubgroupFunctor.range t' := by
    dsimp only [j', t']
    rw [radicalGaloisHom_comp_innerIso, ← SubgroupFunctor.basePoint_smul_range,
      ← SubgroupFunctor.basePoint_smul_range, hgσ, mul_smul, ← basePoint_smul_inf',
      hz, mul_smul, hw, mul_smul, hq']
    rw [show SubgroupFunctor.range j ⊓ q • SubgroupFunctor.range p =
        q • (SubgroupFunctor.range j ⊓ SubgroupFunctor.range p) by
          rw [basePoint_smul_inf', hq],
      hop, ← mul_smul, SubgroupFunctor.basePoint_smul_range]
  let l' := l ≫ (B.innerIso s).hom
  have hl' : l' ≫ j' = t' := by
    dsimp only [l', j', t']
    rw [Category.assoc, ← Category.assoc (B.innerIso s).hom, innerIso_hom_comp, hs,
      Category.assoc, ← Category.assoc l, hl, innerIso_mul_hom]
  refine exists_quadraticOppositeMinimalParabolicLevi_of_intersection hdeg σ hσ j' l'
    (hj.comp_iso ((GQ).innerIso g)) (hlevi.comp_iso (B.innerIso s)) ?_
  rw [hl']
  exact hinter

end Existence

end Langlands.GroupScheme
