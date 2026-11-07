import Langlands.GroupScheme.Reductive.RepresentationWeightsFibreComparison
import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Assemble common fibrewise root data from actual field data -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section IdentityTransport

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} {J : Type v} {J' : Type w}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum J' (characterLattice T) (cocharacterLattice T)}

/-- Reindexing full root data with both lattice maps fixed preserves every
actual-root-datum clause, including the actual reflection normalizers. -/
theorem IsRootDatumOf.of_identityEquiv (hP : IsRootDatumOf i P)
    (e : RootPairing.Equiv P Q)
    (hw : e.toHom.weightMap = LinearMap.id)
    (hc : e.toHom.coweightMap = LinearMap.id) :
    IsRootDatumOf i Q := by
  have hpair : Q.toLinearMap = P.toLinearMap := by
    apply LinearMap.ext
    intro χ
    apply LinearMap.ext
    intro ν
    simpa only [RootPairing.Equiv.weightEquiv_apply,
      RootPairing.Equiv.coweightEquiv_apply, hw, hc, LinearMap.id_apply]
      using e.toLinearMap_weightEquiv χ ν
  have hroot (α : J) : Q.root (e.toHom.indexEquiv α) = P.root α := by
    simpa only [Function.comp_apply, hw, LinearMap.id_apply]
      using (congrFun e.toHom.root_weightMap α).symm
  have hreflection (α : J) : Q.reflection (e.toHom.indexEquiv α) = P.reflection α := by
    apply LinearEquiv.ext
    intro χ
    simpa only [RootPairing.Equiv.weightEquiv_apply, hw, LinearMap.id_apply]
      using (e.weightEquiv_reflection α χ).symm
  refine ⟨hpair.trans hP.1, ?_, ?_⟩
  · rw [← hP.2.1]
    ext χ
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨e.toHom.indexEquiv.symm α, by simp only [← hroot, Equiv.apply_symm_apply]⟩
    · rintro ⟨α, rfl⟩
      exact ⟨e.toHom.indexEquiv α, hroot α⟩
  · intro α
    obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 (e.toHom.indexEquiv.symm α)
    refine ⟨n, σ, hn, hσ.trans ?_⟩
    simpa only [Equiv.apply_symm_apply] using
      (hreflection (e.toHom.indexEquiv.symm α)).symm

end IdentityTransport

namespace CoordinateRootDatum

variable {I : Type u} [Fintype I] {J : Type v}
  (k : Type u) [Field k]
  (P : RootDatum J
    (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))
    (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)))

/-- Express an actual field root datum on the entire coordinate lattices. -/
def ofField : RootDatum J (I → ℤ) (I → ℤ) :=
  P.map (Equiv.refl J) (splitTorus.characterLatticeEquiv k I).toIntLinearEquiv
    (splitTorus.cocharacterLatticeEquiv k I).toIntLinearEquiv

/-- Full equivalence from an actual field datum to its coordinate expression. -/
def ofFieldEquiv : RootPairing.Equiv P (ofField k P) :=
  SplitExistence.rootPairingMapEquiv P
    (splitTorus.characterLatticeEquiv k I).toIntLinearEquiv
    (splitTorus.cocharacterLatticeEquiv k I).toIntLinearEquiv

/-- Returning the coordinate expression to its original field fixes both
entire actual lattices. -/
def fieldRealizationOfFieldEquiv :
    RootPairing.Equiv P (fieldRealization k (ofField k P)) :=
  (fieldRealizationEquiv k (ofField k P)).comp (ofFieldEquiv k P)

@[simp]
theorem fieldRealizationOfFieldEquiv_weightMap :
    (fieldRealizationOfFieldEquiv k P).toHom.weightMap = LinearMap.id := by
  apply LinearMap.ext
  intro χ
  exact (splitTorus.characterLatticeEquiv k I).symm_apply_apply χ

@[simp]
theorem fieldRealizationOfFieldEquiv_coweightMap :
    (fieldRealizationOfFieldEquiv k P).toHom.coweightMap = LinearMap.id := by
  apply LinearMap.ext
  intro ν
  exact (splitTorus.cocharacterLatticeEquiv k I).symm_apply_apply ν

variable {k P}

/-- The coordinate expression realizes the same actual field root datum. -/
theorem isRootDatumOf_fieldRealization_ofField
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
    (hP : IsRootDatumOf i P) :
    IsRootDatumOf i (fieldRealization k (ofField k P)) :=
  hP.of_identityEquiv (fieldRealizationOfFieldEquiv k P)
    (fieldRealizationOfFieldEquiv_weightMap k P)
    (fieldRealizationOfFieldEquiv_coweightMap k P)

theorem ofField_isReduced (hP : P.IsReduced) : (ofField k P).IsReduced := by
  let := hP
  refine ⟨fun α β hdep => ?_⟩
  have hdep' : ¬ LinearIndependent ℤ ![P.root α, P.root β] := by
    intro hli
    apply hdep
    convert hli.map_injOn (splitTorus.characterLatticeEquiv k I).toIntLinearEquiv.toLinearMap
      (splitTorus.characterLatticeEquiv k I).injective.injOn using 1
    ext a
    fin_cases a <;> rfl
  rcases RootPairing.IsReduced.eq_or_eq_neg α β hdep' with h | h
  · left
    change splitTorus.characterLatticeEquiv k I (P.root α) =
      splitTorus.characterLatticeEquiv k I (P.root β)
    rw [h]
  · right
    change splitTorus.characterLatticeEquiv k I (P.root α) =
      -splitTorus.characterLatticeEquiv k I (P.root β)
    rw [h]
    exact (splitTorus.characterLatticeEquiv k I).toAddMonoidHom.map_neg _

variable (k) {J' : Type w}
  {A : RootDatum J (I → ℤ) (I → ℤ)}
  {B : RootDatum J' (I → ℤ) (I → ℤ)}

/-- An identity-lattice coordinate equivalence preserves the actual datum
on any one field realization. -/
theorem isRootDatumOf_of_identityEquiv
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
    (hA : IsRootDatumOf i (fieldRealization k A))
    (e : RootPairing.Equiv A B)
    (hw : e.toHom.weightMap = LinearMap.id)
    (hc : e.toHom.coweightMap = LinearMap.id) :
    IsRootDatumOf i (fieldRealization k B) := by
  let e' := (fieldRealizationEquiv k B).comp (e.comp (fieldRealizationEquiv k A).symm)
  apply hA.of_identityEquiv e'
  · apply LinearMap.ext
    intro χ
    change (fieldRealizationEquiv k B).toHom.weightMap
      (e.toHom.weightMap ((fieldRealizationEquiv k A).symm.toHom.weightMap χ)) = χ
    rw [hw, LinearMap.id_apply]
    exact (fieldRealizationEquiv k A).weightEquiv.apply_symm_apply χ
  · apply LinearMap.ext
    intro ν
    change (fieldRealizationEquiv k A).symm.toHom.coweightMap
      (e.toHom.coweightMap ((fieldRealizationEquiv k B).toHom.coweightMap ν)) = ν
    rw [hc, LinearMap.id_apply]
    exact (fieldRealizationEquiv k A).coweightEquiv.symm_apply_apply ν

end CoordinateRootDatum

section LocalAssembly

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  {N : ℕ} (ρ : MatrixRepresentation G (Fin N))

local instance assemblyFibreAffine {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

/-- A finite reduced datum on one field fibre works on every field fibre
when actual coordinate root data exist there and the supplied integral
representation has monomorphic torus composite. -/
theorem isFibrewiseRootDatumOf_of_fieldData
    (hmono : Mono (i.hom.hom ≫ ρ.hom.hom).left)
    (k : Type u) [Field k] [Algebra R k]
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hfinite : Finite J) (hred : P.IsReduced)
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (CoordinateRootDatum.fieldRealization k P))
    (hfield : ∀ (l : Type u) [Field l] [Algebra R l],
      ∃ (J' : Type u) (Q : RootDatum J' (I → ℤ) (I → ℤ)),
        IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
          (CoordinateRootDatum.fieldRealization l Q)) :
    IsFibrewiseRootDatumOf I G i P := by
  refine ⟨hfinite, hred, fun l _ _ => ?_⟩
  obtain ⟨J', Q, hQ⟩ := hfield l
  let e := CoordinateRootDatum.equivOfRepresentation I G i ρ l Q k P hmono hQ hP
  exact CoordinateRootDatum.isRootDatumOf_of_identityEquiv l hQ e
    (CoordinateRootDatum.equivOfRepresentation_weightMap I G i ρ l Q k P hmono hQ hP)
    (CoordinateRootDatum.equivOfRepresentation_coweightMap I G i ρ l Q k P hmono hQ hP)

/-- Actual finite reduced root data on every field fibre supply one common
finite reduced coordinate datum, chosen on the local residue field. -/
theorem exists_fibrewiseRootDatumOf_of_actualFieldData
    (hmono : Mono (i.hom.hom ≫ ρ.hom.hom).left)
    (hfield : ∀ (k : Type u) [Field k] [Algebra R k],
      ∃ (J : Type u) (_ : Finite J)
        (P : RootDatum J
          (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))
          (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))),
        IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i) P ∧ P.IsReduced) :
    ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P := by
  obtain ⟨J, hJ, P, hP, hred⟩ := hfield (IsLocalRing.ResidueField R)
  refine ⟨J, CoordinateRootDatum.ofField (IsLocalRing.ResidueField R) P,
    isFibrewiseRootDatumOf_of_fieldData I G i ρ hmono
      (IsLocalRing.ResidueField R) _ hJ
      (CoordinateRootDatum.ofField_isReduced hred)
      (CoordinateRootDatum.isRootDatumOf_fieldRealization_ofField hP) ?_⟩
  intro k _ _
  obtain ⟨J', _, Q, hQ, _⟩ := hfield k
  exact ⟨J', CoordinateRootDatum.ofField k Q,
    CoordinateRootDatum.isRootDatumOf_fieldRealization_ofField hQ⟩

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- The field root-datum existence statement, field-fibre maximality and a
supplied integral representation imply common full fibrewise root data. -/
theorem exists_fibrewiseRootDatumOf_of_rootDatumExistence
    (hG : IsReductive G) (hD : RootDatumExistenceStatement.{u})
    (hmono : Mono (i.hom.hom ≫ ρ.hom.hom).left)
    (hmax : ∀ (k : Type u) [Field k] [Algebra R k],
      IsMaximalTorus
        (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
        (splitTorus.baseChangeHom (K := k) G I i)) :
    haveI := hG.isAffineHom
    ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P := by
  let := hG.smooth
  let := hG.isAffineHom
  apply exists_fibrewiseRootDatumOf_of_actualFieldData I G i ρ hmono
  intro k _ _
  exact hD k _ (hG.isConnectedReductive_algebraMap k)
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (isSplitTorus_splitTorus I) _ (hmax k)

end LocalAssembly

end Langlands.GroupScheme
