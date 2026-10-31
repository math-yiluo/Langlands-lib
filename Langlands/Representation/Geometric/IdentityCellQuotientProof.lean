import Langlands.Representation.Geometric.IdentityCellQuotientStatement
import Langlands.Representation.Geometric.CosetOrbitOrdering
import Langlands.Representation.Geometric.OpenOrbitCut
import Langlands.Topology.GroupAction.FiniteOrbitProof
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Geometric.PadicParabolicBruhatProof
import Langlands.Representation.Geometric.ParabolicSupportGradedProof
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Langlands.Representation.Parabolic.QuotientCompactProof

/-! The identity-cell quotient of the normalized geometric lemma (Ze80 1.3). -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G]
  {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G}

namespace RepSubfunctor

/-- A subfunctor that is everything at every object receives the original
functor, by viewing each vector as a vector of the subfunctor. -/
def fromFull (S : RepSubfunctor F) (h : ∀ X, S.obj X = ⊤) : F ⟶ S.toFunctor where
  app X := Rep.ofHom
    { toLinearMap :=
        { toFun := fun v => ⟨v, by rw [h X]; exact Submodule.mem_top⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  naturality _ _ _ := rfl

theorem fromFull_surjective (S : RepSubfunctor F) (h : ∀ X, S.obj X = ⊤) (X : C) :
    Function.Surjective ((S.fromFull h).app X).hom := by
  rintro ⟨v, hv⟩
  exact ⟨v, rfl⟩

end RepSubfunctor

namespace RepFunctorFiltration

variable {n : ℕ}

/-- When the upper step of a graded piece is the last step of the filtration,
the original functor maps naturally onto that graded piece. -/
def lastGradedProjection (s : RepFunctorFiltration F n) (i : Fin n)
    (hi : i.succ = Fin.last n) : F ⟶ s.graded i :=
  (s.step i.succ).fromFull (fun X => by rw [hi]; exact s.top X) ≫
    (s.step i.castSucc).quotientNatProjection (s.step i.succ)

theorem lastGradedProjection_surjective (s : RepFunctorFiltration F n) (i : Fin n)
    (hi : i.succ = Fin.last n) (X : C) :
    Function.Surjective ((s.lastGradedProjection i hi).app X).hom := by
  intro y
  obtain ⟨v, rfl⟩ := (s.step i.castSucc).quotientProjection_surjective (s.step i.succ) X y
  obtain ⟨x, rfl⟩ := (s.step i.succ).fromFull_surjective
    (fun X => by rw [hi]; exact s.top X) X v
  exact ⟨x, rfl⟩

end RepFunctorFiltration

/-- Following an objectwise surjective natural transformation by a natural
isomorphism keeps every component surjective. -/
theorem surjective_app_comp_iso_hom {F₁ F₂ F₃ : C ⥤ Rep.{uV} R G}
    (π : F₁ ⟶ F₂) (e : F₂ ≅ F₃) (X : C)
    (hπ : Function.Surjective (π.app X).hom) :
    Function.Surjective ((π ≫ e.hom).app X).hom := by
  intro y
  obtain ⟨x, hx⟩ := hπ ((e.inv.app X).hom y)
  refine ⟨x, ?_⟩
  change (e.hom.app X).hom ((π.app X).hom x) = y
  rw [hx]
  exact congrArg (fun f => f.hom y) (e.inv_hom_id_app X)

end Langlands

namespace Langlands.Geometric

open GeneralLinear

universe uF uV

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- The orbit of the identity coset is the image of the compact group
`P_C ∩ GL_n(O)`: every element of `P_C` becomes upper triangular after right
multiplication by an integral matrix, which then lies in `P_C`. -/
theorem cosetOrbit_one_eq_image :
    letI := T.topology
    letI := T.valuativeRel
    cosetOrbit (B.parabolic F.Carrier) (C.parabolic F.Carrier) 1 =
      Induction.quotientMap (B.parabolic F.Carrier) ''
        ((C.parabolic F.Carrier : Set (GeneralLinear n F.Carrier)) ∩
          (Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) n :
            Set (GeneralLinear n F.Carrier))) := by
  let := T.topology
  let := T.valuativeRel
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨k, hk, hup⟩ :=
      Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation F.Carrier) n
        (q : GeneralLinear n F.Carrier)
    have hP : (q : GeneralLinear n F.Carrier) * k ∈ B.parabolic F.Carrier :=
      B.mem_parabolic_of_isUpperTriangular _ hup
    have hQ : (q : GeneralLinear n F.Carrier) * k ∈ C.parabolic F.Carrier :=
      C.mem_parabolic_of_isUpperTriangular _ hup
    have hkQ : k ∈ C.parabolic F.Carrier := by
      simpa using (C.parabolic F.Carrier).mul_mem
        ((C.parabolic F.Carrier).inv_mem q.property) hQ
    refine ⟨k⁻¹, ⟨(C.parabolic F.Carrier).inv_mem hkQ, inv_mem hk⟩, ?_⟩
    apply Quotient.sound
    change QuotientGroup.rightRel _ k⁻¹ (1⁻¹ * (q : GeneralLinear n F.Carrier))
    rw [QuotientGroup.rightRel_apply, inv_inv, inv_one, one_mul]
    exact hP
  · rintro ⟨k, ⟨hkQ, -⟩, rfl⟩
    refine ⟨⟨k, hkQ⟩, ?_⟩
    change Induction.quotientMap _ (1⁻¹ * k) = Induction.quotientMap _ k
    rw [inv_one, one_mul]

/-- The identity orbit `P_B \ P_B P_C` is closed in `P_B \ GL_n(F)`. -/
theorem isClosed_cosetOrbit_one :
    letI := T.topology
    IsClosed (cosetOrbit (B.parabolic F.Carrier) (C.parabolic F.Carrier) 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := QuotientIntegration.leftQuotient_t2Space (B.parabolic F.Carrier)
    (B.isClosed_parabolic F.Carrier)
  rw [cosetOrbit_one_eq_image T B C]
  exact (((Parabolic.isCompact_integralRange T n).inter_left
    (C.isClosed_parabolic F.Carrier)).image continuous_quotient_mk').isClosed

/-- The identity permutation as a minimal representative. -/
def identityRepresentative : MinimalRepresentatives B C :=
  ⟨1, fun i => index_strictMono B i, fun j => index_strictMono C j⟩

/-- Changing the refinements along equalities does not change the geometric piece. -/
theorem geometricPieceFunctor_refinement_congr (w : Equiv.Perm (Fin n))
    {S₁ S₂ : BlockRefinement B} {R₁ R₂ : BlockRefinement C}
    (hS : S₁ = S₂) (hR : R₁ = R₂)
    (h₁ : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S₁)
    (h₂ : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R₁)
    (h₃ : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S₂)
    (h₄ : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R₂) :
    geometricPieceFunctor.{uF, uV} T B C w S₁ R₁ h₁ h₂ =
      geometricPieceFunctor.{uF, uV} T B C w S₂ R₂ h₃ h₄ := by
  subst hS
  subst hR
  rfl

end Padic

/-- Zelevinsky 1980, Corollary 1.3: the normalized Jacquet module of the
normalized induced representation maps naturally onto the identity geometric
piece, with surjective components. -/
theorem padicIdentityCellQuotientTheorem :
    PadicIdentityCellQuotientTheorem.{uF, uV} := by
  intro p _ F T n hn B C S R hS hR
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearT2Space n
  let := T.generalLinearSigmaCompactSpace n
  let P := B.parabolic F.Carrier
  let Q := C.parabolic F.Carrier
  have hBruhat := padicParabolicBruhat.{uF} p F n hn B C
  have hfinite : Finite (DoubleCoset.Quotient
      (P : Set (GeneralLinear n F.Carrier)) (Q : Set (GeneralLinear n F.Carrier))) :=
    Finite.of_surjective _ hBruhat.surjective
  obtain ⟨m, ⟨s⟩⟩ :=
    (closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
      Langlands.Topology.finiteOrbitOrdering) (GeneralLinear n F.Carrier)
        P Q (B.isClosed_parabolic F.Carrier) (C.isClosed_parabolic F.Carrier) hfinite
  -- Put the closed identity orbit after every other orbit.
  obtain ⟨a, b, -, t, -, hcut⟩ := s.exists_openCut
    (cosetOrbit P Q 1)ᶜ (isClosed_cosetOrbit_one T B C).isOpen_compl
    (fun i => DoubleCoset.mk P Q 1⁻¹ ≠ DoubleCoset.mk P Q (s.representative i)⁻¹)
    (by
      intro i x hx
      induction x using Quotient.inductionOn with
      | h x =>
        have hx' := (quotientMap_mem_cosetOrbit_iff P Q _ x).mp hx
        change Induction.quotientMap P x ∉ cosetOrbit P Q 1 ↔ _
        rw [quotientMap_mem_cosetOrbit_iff, hx'])
  -- The orbits at or after the cut are exactly the identity double coset.
  have htail : ∀ i : Fin (a + b),
      DoubleCoset.mk P Q (t.representative i)⁻¹ = DoubleCoset.mk P Q 1⁻¹ ↔ a ≤ i.val := by
    intro i
    let x := Induction.quotientMap P (t.representative i)⁻¹
    have hx : x ∈ cosetOrbit P Q (t.representative i) := ⟨1, by simp [x]⟩
    have hcutx : x ∈ t.initialOrbits ⟨a, by omega⟩ ↔ i.val < a := by
      constructor
      · rintro ⟨j, hj, hxj⟩
        have hji : j = i := by
          by_contra hne
          exact Set.disjoint_left.mp (t.disjoint hne) hxj hx
        simpa only [hji] using hj
      · intro hi
        exact ⟨i, hi, hx⟩
    rw [hcut, Set.mem_compl_iff, quotientMap_mem_cosetOrbit_iff] at hcutx
    constructor
    · intro h
      by_contra hlt
      exact (hcutx.mpr (by omega)) h.symm
    · intro h
      by_contra hne
      have := hcutx.mp (fun h' => hne h'.symm)
      omega
  -- Replace the representatives by the minimal permutation matrices.
  let o := minimalPermutationOrdering B C t hBruhat
  let e := o.1
  let u := o.2.val
  have hrep : ∀ i, u.representative i = permutation n F.Carrier (e i).val :=
    o.2.property
  let w₁ := identityRepresentative B C
  have he : ∀ i, e i = w₁ ↔ a ≤ i.val := by
    intro i
    rw [← hBruhat.injective.eq_iff]
    have h₁ : parabolicDoubleCoset F.Carrier B C (e i) =
        DoubleCoset.mk P Q (t.representative i)⁻¹ :=
      (Equiv.ofBijective _ hBruhat).apply_symm_apply (t.doubleCosetEquiv i)
    have h₂ : parabolicDoubleCoset F.Carrier B C w₁ = DoubleCoset.mk P Q 1⁻¹ := by
      change DoubleCoset.mk P Q (permutation n F.Carrier 1)⁻¹ = _
      rw [map_one]
    rw [h₁, h₂]
    exact htail i
  have hb : a < a + b := by
    have := (he (e.symm w₁)).mp (e.apply_symm_apply w₁)
    have := (e.symm w₁).isLt
    omega
  let i : Fin (a + b) := ⟨a + b - 1, by omega⟩
  have hi : i.succ = Fin.last (a + b) := Fin.ext (by simp [i]; omega)
  have hei : e i = w₁ := (he i).mpr (by simp [i]; omega)
  -- Standard intersection refinements, equal to `S` and `R` at the identity.
  choose S₀ hS₀ using fun w =>
    (padicStandardIntersectionsTheorem.{uF} p F n hn B C w).1
  choose R₀ hR₀ using fun w =>
    (padicStandardIntersectionsTheorem.{uF} p F n hn B C w).2
  let S' : MinimalRepresentatives B C → BlockRefinement B :=
    fun w => if w = w₁ then S else S₀ w
  let R' : MinimalRepresentatives B C → BlockRefinement C :=
    fun w => if w = w₁ then R else R₀ w
  have hS' : ∀ w, IsIntersectionRefinement (F := F.Carrier) B C w.val (S' w) := by
    intro w
    by_cases hw : w = w₁
    · subst hw
      rw [show S' w₁ = S from ite_eq_left rfl]
      exact hS
    · rw [show S' w = S₀ w from ite_eq_right hw]
      exact hS₀ w
  have hR' : ∀ w, IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ (R' w) := by
    intro w
    by_cases hw : w = w₁
    · subst hw
      rw [show R' w₁ = R from ite_eq_left rfl]
      exact hR
    · rw [show R' w = R₀ w from ite_eq_right hw]
      exact hR₀ w
  obtain ⟨iso⟩ := padicParabolicSupportGradedTheorem.{uF, uV}
    p F T n hn B C (a + b) e u hrep S' R' hS' hR' i
  have hpiece' : ∀ w, w = w₁ →
      geometricPieceFunctor T B C w.val (S' w) (R' w) (hS' w).2.1 (hR' w).2.1 =
        geometricPieceFunctor T B C 1 S R hS.2.1 hR.2.1 := by
    rintro w rfl
    exact geometricPieceFunctor_refinement_congr T B C 1 (ite_eq_left rfl : S' w₁ = S)
      (ite_eq_left rfl : R' w₁ = R) _ _ _ _
  have hpiece := hpiece' (e i) hei
  rw [← hpiece]
  exact ⟨(parabolicJacquetSupportFiltration.{uF, uV} T B C u).lastGradedProjection i hi ≫
      iso.hom, fun A => surjective_app_comp_iso_hom _ iso A
    ((parabolicJacquetSupportFiltration.{uF, uV} T B C u).lastGradedProjection_surjective
      i hi A)⟩

end Langlands.Geometric
