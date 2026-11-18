import Langlands.GroupScheme.RelativeUnipotent.RootWeightConjugationLayer
import Langlands.GroupScheme.RelativeUnipotent.LinearQuotientComparison
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

/-! # Parabolic conjugation is linear on actual vector layers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.FppfQuotientComparison

variable {S : Scheme.{u}} {H G Q : GroupScheme S}

/-- Equivariance modulo the full quotient kernel suffices for the actual
descended map to be equivariant. -/
theorem isEquivariant_of_fac_mod_kernel
    {q : G ⟶ Q} {F : SubgroupFunctor G} [QuasiCompact q.hom.hom.left]
    (hq : RelativeRoot.IsFppfQuotient F q)
    (a : AutomorphicAction H G) (b : AutomorphicAction H Q)
    (haq : a.IsEquivariant b q)
    (e : G ⟶ G) (E : Q ⟶ Q) (hE : q ≫ E = e ≫ q)
    (hmod : ∀ (T : Over S) (s : T ⟶ H.X) (x : T ⟶ G.X),
      (a.act s x ≫ e.hom.hom) ≫ q.hom.hom =
        b.act s ((x ≫ e.hom.hom) ≫ q.hom.hom)) :
    b.IsEquivariant b E := by
  have := hq.1
  have := hq.2.1
  have hf : q.hom.hom ≫ E.hom.hom = e.hom.hom ≫ q.hom.hom :=
    congrArg (fun f => f.hom.hom) hE
  intro T s x
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q x
  intro V f y hfy
  calc
    f ≫ (b.act s x ≫ E.hom.hom) =
        (a.act (f ≫ s) y ≫ e.hom.hom) ≫ q.hom.hom := by
      rw [← Category.assoc, b.naturality, hfy, ← haq]
      rw [Category.assoc, hf, ← Category.assoc]
    _ = b.act (f ≫ s) ((y ≫ e.hom.hom) ≫ q.hom.hom) := hmod V (f ≫ s) y
    _ = f ≫ b.act s (x ≫ E.hom.hom) := by
      rw [b.naturality, ← Category.assoc, hfy]
      simp only [Category.assoc]
      rw [hf]

end Langlands.GroupScheme.FppfQuotientComparison

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

variable {R : Type u} [CommRing R]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {C : RootHeightChart U} (W : RootWeightData C)
  (j : U ⟶ G) [Mono j.hom.hom]
  (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)
  (hrep : (Dynamic.unipotent χ).IsRepresentedBy (W.inclusion 0 ≫ j))

include hrep

/-- The full contracting subgroup acts trivially on each layer whenever its
actual representative is the first positive term. -/
theorem quotientMap_eq_of_unipotent_conjugation
    (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    {z : T ⟶ G.X} (hz : z ∈ (Dynamic.unipotent χ).carrier T)
    (x y : T ⟶ (W.groupScheme d).X)
    (hy : y ≫ (W.inclusion d ≫ j).hom.hom =
      z * (x ≫ (W.inclusion d ≫ j).hom.hom) * z⁻¹) :
    y ≫ (W.quotientMap d).hom.hom = x ≫ (W.quotientMap d).hom.hom := by
  rw [← hrep.2] at hz
  obtain ⟨z₀, hz₀⟩ := SubgroupFunctor.mem_range.mp hz
  have hzU : z₀ ≫ (W.inclusion 0).hom.hom ∈ (W.subgroup 0).carrier T :=
    ((W.isRepresentedBy_inclusion 0).pointsEquiv T z₀).property
  apply W.quotientMap_eq_of_positive_conjugation T d hzU x y
  apply (cancel_mono j.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  have hs : (z₀ ≫ (W.inclusion 0).hom.hom) ≫ j.hom.hom = z := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using hz₀
  rw [hs]
  simpa only [Grp.comp_hom_hom, Category.assoc] using hy

variable [IsSeparated G.X.hom]
  (d : ℕ)
  (hnorm : (SubgroupFunctor.range (W.inclusion d ≫ j)).IsNormalizedBy (Dynamic.parabolic χ))
  (a : AutomorphicAction (Gm (Spec (CommRingCat.of R))).toGrp (W.groupScheme d))
  (ha : ∀ (T : Over (Spec (CommRingCat.of R)))
    (s : T ⟶ (Gm (Spec (CommRingCat.of R))).X) (x : T ⟶ (W.groupScheme d).X),
    a.act s x ≫ (W.inclusion d ≫ j).hom.hom =
      (s ≫ χ.hom.hom) * (x ≫ (W.inclusion d ≫ j).hom.hom) * (s ≫ χ.hom.hom)⁻¹)
  (N : ℕ)
  (haq : a.IsEquivariant
    (VectorGroup.powerWeightAction (Nat.card (W.exactSupport d)) N) (W.quotientMap d))

include hrep hnorm ha haq

/-- On the actual quotient, arbitrary parabolic conjugation commutes with the
cocharacter action; the parabolic point itself need not centralize the cocharacter. -/
theorem quotientMap_parabolic_scalar
    (T : Over (Spec (CommRingCat.of R)))
    (p : (Dynamic.parabolic χ).carrier T)
    (s : T ⟶ (Gm (Spec (CommRingCat.of R))).X)
    (x y ys : T ⟶ (W.groupScheme d).X)
    (hy : y ≫ (W.inclusion d ≫ j).hom.hom =
      (p : T ⟶ G.X) * (x ≫ (W.inclusion d ≫ j).hom.hom) * (p : T ⟶ G.X)⁻¹)
    (hys : ys ≫ (W.inclusion d ≫ j).hom.hom =
      (p : T ⟶ G.X) * (a.act s x ≫ (W.inclusion d ≫ j).hom.hom) * (p : T ⟶ G.X)⁻¹) :
    ys ≫ (W.quotientMap d).hom.hom =
      (VectorGroup.powerWeightAction (Nat.card (W.exactSupport d)) N).act s
        (y ≫ (W.quotientMap d).hom.hom) := by
  let z := Dynamic.limit χ p
  have hz : z ∈ (Dynamic.centralizer χ).carrier T := Dynamic.limit_mem_centralizer χ p
  have hzP := Dynamic.centralizer_le_parabolic χ T hz
  have hx : x ≫ (W.inclusion d ≫ j).hom.hom ∈
      (SubgroupFunctor.range (W.inclusion d ≫ j)).carrier T :=
    SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  obtain ⟨xz, hxz⟩ := SubgroupFunctor.mem_range.mp
    (hnorm T z _ hzP hx)
  have hu : (p : T ⟶ G.X) * z⁻¹ ∈ (Dynamic.unipotent χ).carrier T :=
    Dynamic.mul_inv_limit_mem_unipotent χ p
  have hqy : y ≫ (W.quotientMap d).hom.hom = xz ≫ (W.quotientMap d).hom.hom := by
    apply W.quotientMap_eq_of_unipotent_conjugation j χ hrep d T hu xz y
    rw [hy, hxz]
    group
  have hcomm := Dynamic.commute_cocharacter_of_mem_centralizer χ hz s
  have hcz : a.act s xz ≫ (W.inclusion d ≫ j).hom.hom =
      z * (a.act s x ≫ (W.inclusion d ≫ j).hom.hom) * z⁻¹ := by
    rw [ha, ha, hxz]
    exact (Corepresented.conj_conj_of_commute hcomm.eq _).symm
  have hqys : ys ≫ (W.quotientMap d).hom.hom =
      a.act s xz ≫ (W.quotientMap d).hom.hom := by
    apply W.quotientMap_eq_of_unipotent_conjugation j χ hrep d T hu (a.act s xz) ys
    rw [hys, hcz]
    group
  rw [hqys, haq, ← hqy]

omit hrep hnorm ha haq in
/-- The actual layer isomorphism induced by compatible consecutive-term automorphisms. -/
def conjugationQuotientIso
    (e : W.groupScheme d ≅ W.groupScheme d)
    (eK : W.groupScheme (d + 1) ≅ W.groupScheme (d + 1))
    (hs : W.step d ≫ e.hom = eK.hom ≫ W.step d) :
    VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (W.exactSupport d)) ≅
      VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (W.exactSupport d)) :=
  FppfQuotientComparison.isoOfCompatibleTerms (W.step d) (W.step d)
    (W.isFppfQuotient_quotientMap d) (W.isFppfQuotient_quotientMap d) e eK hs

omit hrep hnorm ha haq in
/-- The constructed automorphism is the descent of the actual term automorphism. -/
theorem conjugationQuotientIso_fac
    (e : W.groupScheme d ≅ W.groupScheme d)
    (eK : W.groupScheme (d + 1) ≅ W.groupScheme (d + 1))
    (hs : W.step d ≫ e.hom = eK.hom ≫ W.step d) :
    W.quotientMap d ≫ (W.conjugationQuotientIso d e eK hs).hom =
      e.hom ≫ W.quotientMap d :=
  FppfQuotientComparison.isoOfCompatibleTerms_fac (W.step d) (W.step d)
    (W.isFppfQuotient_quotientMap d) (W.isFppfQuotient_quotientMap d) e eK hs

variable
  (p : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X)
  (hp : p ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)))
  (e : W.groupScheme d ≅ W.groupScheme d)
  (eK : W.groupScheme (d + 1) ≅ W.groupScheme (d + 1))
  (hs : W.step d ≫ e.hom = eK.hom ≫ W.step d)
  (he : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (W.groupScheme d).X),
    (x ≫ e.hom.hom.hom) ≫ (W.inclusion d ≫ j).hom.hom =
      G.constantPoint p T * (x ≫ (W.inclusion d ≫ j).hom.hom) * (G.constantPoint p T)⁻¹)

include hp he

/-- Conjugation by any parabolic base point gives a scalar-equivariant actual
vector-layer automorphism, after quotienting; centrality of that point is not assumed. -/
theorem conjugationQuotientIso_isEquivariant :
    (VectorGroup.powerWeightAction (Nat.card (W.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (W.exactSupport d)) N)
      (W.conjugationQuotientIso d e eK hs).hom := by
  let E := W.conjugationQuotientIso d e eK hs
  let b := VectorGroup.powerWeightAction (R := CommRingCat.of R)
    (Nat.card (W.exactSupport d)) N
  change b.IsEquivariant b E.hom
  have hAffine (n : ℕ) :
      IsAffine (VectorGroup.groupScheme (CommRingCat.of R) n).X.left := by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) R)))
    infer_instance
  have := hAffine (Nat.card (W.support d))
  have := hAffine (Nat.card (W.exactSupport d))
  have : QuasiCompact (W.quotientMap d).hom.hom.left := by
    rw [W.quotientMap_hom]
    infer_instance
  apply FppfQuotientComparison.isEquivariant_of_fac_mod_kernel
    (W.isFppfQuotient_quotientMap d) a b haq e.hom E.hom
    (W.conjugationQuotientIso_fac d e eK hs)
  intro V s y
  have hpV : G.constantPoint p V ∈ (Dynamic.parabolic χ).carrier V :=
    (Dynamic.parabolic χ).comp_mem
      (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) (T' := V)
      (Over.homMk V.hom (Category.comp_id V.hom)) hp
  exact W.quotientMap_parabolic_scalar j χ hrep d hnorm a ha N haq V
    ⟨G.constantPoint p V, hpV⟩ s y (y ≫ e.hom.hom.hom)
    (a.act s y ≫ e.hom.hom.hom) (he V y) (he V (a.act s y))

/-- The all-algebra scalar-weight premise is derived for the actual parabolic quotient map. -/
theorem conjugationQuotientIso_hasScalarWeight :
    VectorGroup.HasScalarWeight
      (VectorGroup.pointTransformation (W.conjugationQuotientIso d e eK hs).hom) N :=
  VectorGroup.hasScalarWeight_of_equivariant _ N
    (W.conjugationQuotientIso_isEquivariant j χ hrep d hnorm a ha N haq p hp e eK hs he)

/-- The actual parabolic quotient automorphism is linear over every coefficient algebra. -/
def parabolicLayerLinearEquiv (hN : 0 < N) (A : CommAlgCat.{u} (CommRingCat.of R)) :
    (Fin (Nat.card (W.exactSupport d)) → A) ≃ₗ[A]
      (Fin (Nat.card (W.exactSupport d)) → A) :=
  VectorGroup.linearEquivOfWeight (W.conjugationQuotientIso d e eK hs) hN
    (W.conjugationQuotientIso_hasScalarWeight j χ hrep d hnorm a ha N haq p hp e eK hs he) A

/-- The original actual parabolic quotient automorphism is its base-ring matrix map. -/
theorem conjugationQuotientIso_eq_matrixHom (hN : 0 < N) :
    (W.conjugationQuotientIso d e eK hs).hom =
      VectorGroup.matrixHom (VectorGroup.weightMatrix
        (VectorGroup.pointTransformation (W.conjugationQuotientIso d e eK hs).hom)) :=
  VectorGroup.eq_matrixHom_of_hasScalarWeight _ hN
    (W.conjugationQuotientIso_hasScalarWeight j χ hrep d hnorm a ha N haq p hp e eK hs he)

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
