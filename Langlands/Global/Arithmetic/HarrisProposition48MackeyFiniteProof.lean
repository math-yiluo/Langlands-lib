import Langlands.Global.Arithmetic.HarrisProposition48MackeyData
import Langlands.Global.Arithmetic.HarrisProposition48StabilizerComparison
import Langlands.Global.Arithmetic.HarrisProposition48MackeyChildCompletion
import Langlands.Global.HeckeCharacterTransport
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.ClassFieldTheory.Global.CompletionTower
import Langlands.ClassFieldTheory.Local.FiniteArtinTransport

/-! # The auxiliary finite component of the Mackey character -/

noncomputable section

universe uF

namespace Langlands.Global.Harris.Proposition48Problem

open NumberField IsDedekindDomain AdelicFunctoriality LocalFactor.CommonClosure
open LocalClassField GeneralPosition Langlands.ClassFieldTheory.Global
open scoped FiniteExtension

/-- The parent auxiliary inducing place carried to the actual conjugate field. -/
abbrev mackeyConjugatePlace (Q : Proposition48Problem.{uF}) (a : Q.L ≃ₐ[Q.E] Q.L) :
    FinitePlace (Q.conjugateField a) :=
  finitePlaceEquiv (K := Q.conjugateField a)
    (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv.symm Q.Ps.v'

/-- The completed inverse of the conjugate embedding at the auxiliary place. -/
abbrev mackeyConjugateCompletionEquiv (Q : Proposition48Problem.{uF})
    (a : Q.L ≃ₐ[Q.E] Q.L) :
    FiniteCompletion (Q.conjugateField a) (Q.mackeyConjugatePlace a) ≃+*
      FiniteCompletion Q.E' Q.Ps.v' :=
  finiteCompletionEquiv (K := Q.conjugateField a)
    (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv.symm Q.Ps.v'

theorem mackeyConjugatePlace_liesOver (Q : Proposition48Problem.{uF})
    (a : Q.L ≃ₐ[Q.E] Q.L) :
    (Q.mackeyConjugatePlace a).asIdeal.LiesOver Q.Ps.v.asIdeal := by
  have h := finitePlaceEquiv_liesOver (L := Q.conjugateField a) (RingEquiv.refl Q.E)
      (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv.symm
      (Q.conjugateEmbedding a).equivFieldRange.symm.commutes Q.Ps.v Q.Ps.v'
  rw [finitePlaceEquiv_refl, Equiv.refl_apply] at h
  exact h

private theorem liesOver_of_subsingleton {E A C : Type*} [Field E] [Field A] [Field C]
    [NumberField E] [NumberField A] [NumberField C]
    [Algebra E A] [Algebra A C] [Algebra E C] [IsScalarTower E A C]
    (v : FinitePlace E) (w : FinitePlace A) (q : FinitePlace C)
    (hw : w.asIdeal.LiesOver v.asIdeal) (hq : q.asIdeal.LiesOver v.asIdeal)
    [Subsingleton (FinitePlacesAbove A v)] : q.asIdeal.LiesOver w.asIdeal := by
  let r := q.under (𝓞 A)
  have hqr : q.asIdeal.LiesOver r.asIdeal := ⟨rfl⟩
  have hrv : r.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.tower_bot q.asIdeal r.asIdeal v.asIdeal
  have hrw : r = w := congrArg Subtype.val
    (Subsingleton.elim (⟨r, hrv⟩ : FinitePlacesAbove A v) ⟨w, hw⟩)
  exact hrw ▸ hqr

/-- Every compositum place above the parent auxiliary place lies over the transported place. -/
theorem mackeyPlace_liesOver (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L)
    (w : FinitePlace (Q.mackeyField D a)) (hw : w.asIdeal.LiesOver Q.Ps.v.asIdeal)
    (hQ : HasUniquePlaceAbove Q.L Q.Ps.v) :
    letI : Algebra (Q.conjugateField a) (Q.mackeyField D a) :=
      (IntermediateField.inclusion le_sup_right).toAlgebra
    w.asIdeal.LiesOver (Q.mackeyConjugatePlace a).asIdeal := by
  let : Algebra (Q.conjugateField a) (Q.mackeyField D a) :=
    (IntermediateField.inclusion le_sup_right).toAlgebra
  let : IsScalarTower Q.E (Q.conjugateField a) (Q.mackeyField D a) :=
    .of_algebraMap_eq' rfl
  let : Subsingleton (FinitePlacesAbove (Q.conjugateField a) Q.Ps.v) :=
    finitePlacesAbove_subsingleton (L := Q.L) Q.Ps.v hQ
  exact liesOver_of_subsingleton Q.Ps.v (Q.mackeyConjugatePlace a) w
    (Q.mackeyConjugatePlace_liesOver a) hw

/-- The top auxiliary place also lies over the transported place. -/
theorem mackeyConjugatePlace_liesUnder (Q : Proposition48Problem.{uF})
    (a : Q.L ≃ₐ[Q.E] Q.L) (hQ : HasUniquePlaceAbove Q.L Q.Ps.v) :
    Q.Ps.vTilde.asIdeal.LiesOver (Q.mackeyConjugatePlace a).asIdeal := by
  let : Subsingleton (FinitePlacesAbove (Q.conjugateField a) Q.Ps.v) :=
    finitePlacesAbove_subsingleton (L := Q.L) Q.Ps.v hQ
  exact liesOver_of_subsingleton Q.Ps.v (Q.mackeyConjugatePlace a) Q.Ps.vTilde
    (Q.mackeyConjugatePlace_liesOver a) Q.Ps.liesOver_vTilde

/-- Pulling back the parent character first by conjugation and then by the norm gives the
indicated finite component on the actual Mackey field. -/
theorem mackeyCharacter_finiteComponent (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L)
    (w : FinitePlace (Q.mackeyField D a)) (x : (FiniteCompletion (Q.mackeyField D a) w)ˣ) :
    letI : Algebra (Q.conjugateField a) (Q.mackeyField D a) :=
      (IntermediateField.inclusion le_sup_right).toAlgebra
    ∀ [w.asIdeal.LiesOver (Q.mackeyConjugatePlace a).asIdeal],
      (Q.mackeyCharacter D a).finiteComponent w x =
        Q.ξ.finiteComponent Q.Ps.v'
          (Units.mapEquiv (Q.mackeyConjugateCompletionEquiv a).toMulEquiv
            (FiniteExtension.localUnitNorm (Q.mackeyConjugatePlace a) w x)) := by
  let : Algebra (Q.conjugateField a) (Q.mackeyField D a) :=
    (IntermediateField.inclusion le_sup_right).toAlgebra
  intro hw
  exact (HeckeCharacter.normComp_finiteComponent (L := Q.mackeyField D a) (Q.conjugateCharacter a)
    (Q.mackeyConjugatePlace a) ⟨w, hw⟩ x).trans <|
      HeckeCharacter.comap_finiteComponent (K := Q.conjugateField a)
        (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv.symm Q.ξ Q.Ps.v' _

/-- The inverse conjugation between the inducing completions agrees with inverse
conjugation on the completed normal closure. -/
theorem mackeyConjugateCompletionEquiv_comm (Q : Proposition48Problem.{uF})
    (a : Q.L ≃ₐ[Q.E] Q.L)
    [Q.Ps.vTilde.asIdeal.LiesOver (Q.mackeyConjugatePlace a).asIdeal]
    (σ : FiniteCompletion Q.L Q.Ps.vTilde ≃+* FiniteCompletion Q.L Q.Ps.vTilde)
    (hσ : Continuous σ)
    (hσa : ∀ y : Q.L, σ (algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) y) =
      algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) (a.symm y))
    (x : FiniteCompletion (Q.conjugateField a) (Q.mackeyConjugatePlace a)) :
    FiniteExtension.completionMap Q.Ps.v' Q.Ps.vTilde (Q.mackeyConjugateCompletionEquiv a x) =
      σ (FiniteExtension.completionMap (Q.mackeyConjugatePlace a) Q.Ps.vTilde x) := by
  refine congrFun (((Q.mackeyConjugatePlace a).denseRange_algebraMap (Q.conjugateField a)).equalizer
    ((FiniteExtension.continuous_completionMap Q.Ps.v' Q.Ps.vTilde).comp
      (continuous_finiteCompletionEquiv (K := Q.conjugateField a)
        (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv.symm Q.Ps.v'))
    (hσ.comp (FiniteExtension.continuous_completionMap (Q.mackeyConjugatePlace a) Q.Ps.vTilde))
    (funext fun y => ?_)) x
  change FiniteExtension.completionMap Q.Ps.v' Q.Ps.vTilde
      (Q.mackeyConjugateCompletionEquiv a
        (algebraMap (Q.conjugateField a)
          (FiniteCompletion (Q.conjugateField a) (Q.mackeyConjugatePlace a)) y)) =
    σ (FiniteExtension.completionMap (Q.mackeyConjugatePlace a) Q.Ps.vTilde
      (algebraMap (Q.conjugateField a)
        (FiniteCompletion (Q.conjugateField a) (Q.mackeyConjugatePlace a)) y))
  have h := finiteCompletionEquiv_coe (K := Q.conjugateField a)
    (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv.symm Q.Ps.v' y
  erw [h, FiniteExtension.completionMap_coe, FiniteExtension.completionMap_coe, hσa]
  apply congrArg (algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde))
  apply a.injective
  rw [a.apply_symm_apply]
  exact congrArg (fun z : Q.conjugateField a => (z : Q.L))
    ((Q.conjugateEmbedding a).equivFieldRange.apply_symm_apply y)

section LocalNorm

variable (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
  (a : Q.L ≃ₐ[Q.E] Q.L)

/-- The place on the literal compositum below the parent auxiliary top place. -/
abbrev mackeyFinitePlace : FinitePlace (Q.mackeyField D a) :=
  Q.Ps.vTilde.under (𝓞 (Q.mackeyField D a))

local instance : Algebra (Q.conjugateField a) (Q.mackeyField D a) :=
  (IntermediateField.inclusion le_sup_right).toAlgebra

local instance : IsScalarTower (Q.conjugateField a) (Q.mackeyField D a) Q.L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance [Q.Ps.vTilde.asIdeal.LiesOver (Q.mackeyConjugatePlace a).asIdeal] :
    (Q.mackeyFinitePlace D a).asIdeal.LiesOver (Q.mackeyConjugatePlace a).asIdeal :=
  Ideal.LiesOver.tower_bot Q.Ps.vTilde.asIdeal (Q.mackeyFinitePlace D a).asIdeal
    (Q.mackeyConjugatePlace a).asIdeal

private def parentInducingEquiv (hP : Q.Ps.IsCompatible) :
    FiniteCompletion Q.E' Q.Ps.v' ≃+* Q.F'.field := by
  let f := (galoisClosure Q.F Q.F').field.val.toRingHom.comp
    (Q.Ps.isoTilde.toRingHom.comp (FiniteExtension.completionMap Q.Ps.v' Q.Ps.vTilde))
  have hRange : Set.range f = (Q.F'.field : Set (AlgebraicClosure Q.F.Carrier)) := hP.2
  let g := f.codRestrict Q.F'.field fun x => by
    change f x ∈ (Q.F'.field : Set (AlgebraicClosure Q.F.Carrier))
    rw [← hRange]
    exact Set.mem_range_self x
  refine RingEquiv.ofBijective g ⟨g.injective, ?_⟩
  intro y
  have hy : (y : AlgebraicClosure Q.F.Carrier) ∈ Set.range f := hRange.symm ▸ y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

variable (τ : Field.absoluteGaloisGroup Q.F.Carrier) (hP : Q.Ps.IsCompatible)

private def conjugateInducingEquiv :
    FiniteCompletion (Q.conjugateField a) (Q.mackeyConjugatePlace a) ≃+*
      (Q.F'.conj τ).field :=
  (Q.mackeyConjugateCompletionEquiv a).trans <|
    (parentInducingEquiv Q hP).trans <|
      (IntermediateField.equivMap Q.F'.field τ.toAlgHom).toRingEquiv

private theorem conjugateInducingEquiv_apply
    [Q.Ps.vTilde.asIdeal.LiesOver (Q.mackeyConjugatePlace a).asIdeal]
    (σ : FiniteCompletion Q.L Q.Ps.vTilde ≃+* FiniteCompletion Q.L Q.Ps.vTilde)
    (hσ : Continuous σ)
    (hσa : ∀ y : Q.L, σ (algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) y) =
      algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) (a.symm y))
    (hστ : ∀ y, (Q.Ps.isoTilde (σ y) : AlgebraicClosure Q.F.Carrier) =
      τ.symm (Q.Ps.isoTilde y))
    (x : FiniteCompletion (Q.conjugateField a) (Q.mackeyConjugatePlace a)) :
    (conjugateInducingEquiv Q a τ hP x : AlgebraicClosure Q.F.Carrier) =
      Q.Ps.isoTilde (FiniteExtension.completionMap (Q.mackeyConjugatePlace a) Q.Ps.vTilde x) := by
  change τ.toAlgHom (Q.Ps.isoTilde (FiniteExtension.completionMap Q.Ps.v' Q.Ps.vTilde
    (Q.mackeyConjugateCompletionEquiv a x))) = _
  rw [Q.mackeyConjugateCompletionEquiv_comm a σ hσ hσa, hστ]
  exact AlgEquiv.apply_symm_apply τ _

include hP in
/-- Identify the auxiliary component of the literal Mackey character with the
norm to the conjugate inducing field in the parent's local closure. -/
theorem mackeyCharacter_finiteComponent_localNorm
    [Q.Ps.vTilde.asIdeal.LiesOver (Q.mackeyConjugatePlace a).asIdeal]
    (σ : FiniteCompletion Q.L Q.Ps.vTilde ≃+* FiniteCompletion Q.L Q.Ps.vTilde)
    (hσ : Continuous σ)
    (hσa : ∀ y : Q.L, σ (algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) y) =
      algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) (a.symm y))
    (hστ : ∀ y, (Q.Ps.isoTilde (σ y) : AlgebraicClosure Q.F.Carrier) =
      τ.symm (Q.Ps.isoTilde y))
    (U : Extension Q.F) (eU : FiniteCompletion (Q.mackeyField D a)
      (Q.mackeyFinitePlace D a) ≃+* U.field)
    (heU : ∀ x, (eU x : AlgebraicClosure Q.F.Carrier) =
      Q.Ps.isoTilde (FiniteExtension.completionMap (Q.mackeyFinitePlace D a) Q.Ps.vTilde x))
    (h : (Q.F'.conj τ).field ≤ U.field) (hχ : Q.Ps.HasComponent Q.ξ Q.χs)
    (x : (FiniteCompletion (Q.mackeyField D a) (Q.mackeyFinitePlace D a))ˣ) :
    (Q.mackeyCharacter D a).finiteComponent (Q.mackeyFinitePlace D a) x =
      Q.χs (Units.mapEquiv (IntermediateField.equivMap Q.F'.field τ.toAlgHom).symm.toMulEquiv
        ((Q.F'.conj τ).unitsNorm U h (Units.mapEquiv eU.toMulEquiv x))) := by
  let B := Q.F'.conj τ
  let eB := conjugateInducingEquiv Q a τ hP
  let : Algebra B.field U.field := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower Q.F.Carrier B.field U.field := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional B.field U.field := FiniteDimensional.right Q.F.Carrier B.field U.field
  have he : (algebraMap B.field U.field).comp eB.toRingHom =
      eU.toRingHom.comp (FiniteExtension.completionMap (Q.mackeyConjugatePlace a)
        (Q.mackeyFinitePlace D a)) := by
    apply RingHom.ext
    intro y
    apply Subtype.ext
    change (eB y : AlgebraicClosure Q.F.Carrier) = (eU (FiniteExtension.completionMap
      (Q.mackeyConjugatePlace a) (Q.mackeyFinitePlace D a) y) : AlgebraicClosure Q.F.Carrier)
    rw [conjugateInducingEquiv_apply Q a τ hP σ hσ hσa hστ, heU]
    exact congrArg (fun z : FiniteCompletion Q.L Q.Ps.vTilde =>
      (Q.Ps.isoTilde z : AlgebraicClosure Q.F.Carrier))
      (DFunLike.congr_fun (CompletionTower.completionMap_comp (Q.mackeyConjugatePlace a)
        (Q.mackeyFinitePlace D a) Q.Ps.vTilde) y).symm
  let z := FiniteExtension.localUnitNorm (Q.mackeyConjugatePlace a) (Q.mackeyFinitePlace D a) x
  have hn := FiniteArtinTransport.normUnits_map eB eU he x
  change B.unitsNorm U h (Units.mapEquiv eU.toMulEquiv x) = Units.mapEquiv eB.toMulEquiv z at hn
  rw [hn]
  refine (Q.mackeyCharacter_finiteComponent D a (Q.mackeyFinitePlace D a) x).trans (hχ _ _ ?_)
  let c := IntermediateField.equivMap Q.F'.field τ.toAlgHom
  let t := Q.mackeyConjugateCompletionEquiv a (z : FiniteCompletion (Q.conjugateField a)
    (Q.mackeyConjugatePlace a))
  change ((c.symm (c (parentInducingEquiv Q hP t)) : Q.F'.field) :
    AlgebraicClosure Q.F.Carrier) = _
  rw [c.symm_apply_apply]
  rfl

end LocalNorm

section CompletionImage

variable (Q : Proposition48Problem.{uF}) (hP : Q.Ps.IsCompatible)

local notation "w" => Q.Ps.vTilde

private abbrev auxiliaryTopEmbedding :
    FiniteCompletion Q.L w →+* AlgebraicClosure Q.F.Carrier :=
  (galoisClosure Q.F Q.F').field.val.toRingHom.comp Q.Ps.isoTilde.toRingHom

local notation "f" => (auxiliaryTopEmbedding Q)

private def auxiliaryCompletedField (B : IntermediateField Q.E Q.L) :
    IntermediateField Q.F.Carrier (AlgebraicClosure Q.F.Carrier) :=
  MackeyCompletion.mapField Q.Ps.iso f
    (fun x => congrArg Subtype.val (hP.1 x))
    (MackeyCompletion.completedField Q.Ps.v w B)

private theorem auxiliaryCompletedField_eq (B : IntermediateField Q.E Q.L)
    (b : FinitePlace B) [(w).asIdeal.LiesOver b.asIdeal]
    (V : IntermediateField Q.F.Carrier (AlgebraicClosure Q.F.Carrier))
    (e : FiniteCompletion B b ≃+* V)
    (he : ∀ x, (e x : AlgebraicClosure Q.F.Carrier) =
      Q.Ps.isoTilde (FiniteExtension.completionMap b w x)) :
    Q.auxiliaryCompletedField hP B = V := by
  have hb : b = (w).under (𝓞 B) :=
    IsDedekindDomain.HeightOneSpectrum.ext (Ideal.LiesOver.over (P := (w).asIdeal)
      (p := b.asIdeal))
  subst b
  let := MackeyCompletion.under_liesOver Q.Ps.v w B
  ext x
  change (∃ y ∈ MackeyCompletion.completedField Q.Ps.v w B, f y = x) ↔ x ∈ V
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (MackeyCompletion.mem_image_iff Q.Ps.v ((w).under (𝓞 B)) w y).mp hy
    change (Q.Ps.isoTilde (FiniteExtension.completionMap ((w).under (𝓞 B)) w z) :
      AlgebraicClosure Q.F.Carrier) ∈ V
    rw [← he z]
    exact (e z).2
  · intro hx
    obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
    refine ⟨FiniteExtension.completionMap ((w).under (𝓞 B)) w z, ⟨z, rfl⟩, ?_⟩
    exact (he z).symm.trans (congrArg Subtype.val hz)

private theorem auxiliaryCompletedField_sup [IsGalois Q.E Q.L]
    (hQ : HasUniquePlaceAbove Q.L Q.Ps.v) (B C : IntermediateField Q.E Q.L) :
    Q.auxiliaryCompletedField hP (B ⊔ C) =
      Q.auxiliaryCompletedField hP B ⊔ Q.auxiliaryCompletedField hP C := by
  have h := (MackeyCompletion.intermediateFieldEquiv Q.Ps.v w hQ).map_sup B C
  change MackeyCompletion.completedField Q.Ps.v w (B ⊔ C) =
    MackeyCompletion.completedField Q.Ps.v w B ⊔ MackeyCompletion.completedField Q.Ps.v w C at h
  apply IntermediateField.toSubfield_injective
  rw [IntermediateField.sup_toSubfield]
  change (MackeyCompletion.completedField Q.Ps.v w (B ⊔ C)).toSubfield.map f = _
  rw [h, IntermediateField.sup_toSubfield, Subfield.map_sup]
  rfl

end CompletionImage

end Langlands.Global.Harris.Proposition48Problem

namespace Langlands.Global.Harris.MackeyChild.CompletedBase

open NumberField AdelicFunctoriality LocalFactor.CommonClosure Weil.Local

variable {Q : Proposition48Problem.{uF}} {D : IntermediateField Q.E Q.L}
  {T : Extension Q.F} (A : CompletedBase Q D T) (a : Q.L ≃ₐ[Q.E] Q.L)

/-- The child's completed inducing field as a subfield of the specified parent closure. -/
abbrev parentInducingField : IntermediateField Q.F.Carrier (AlgebraicClosure Q.F.Carrier) :=
  ((A.localInducing a).field.map (intermediateClosureEquiv Q.F T).toAlgHom).restrictScalars
    Q.F.Carrier

/-- The child-to-parent identification is induced by the chosen common-closure isomorphism. -/
def parentInducingEquiv : (A.localInducing a).field ≃+* A.parentInducingField a :=
  (IntermediateField.equivMap (A.localInducing a).field
    (intermediateClosureEquiv Q.F T).toAlgHom).toRingEquiv

theorem parentInducingEquiv_apply (y : (A.localInducing a).field) :
    (A.parentInducingEquiv a y : AlgebraicClosure Q.F.Carrier) =
      intermediateClosureEquiv Q.F T (y : AlgebraicClosure T.field) :=
  rfl

private theorem parentInducingEquiv_localEquiv_apply
    (x : FiniteCompletion (inducingField Q D a) (inducingPlace Q D a)) :
    (A.parentInducingEquiv a (A.localEquiv (inducingField Q D a) x) :
      AlgebraicClosure Q.F.Carrier) =
      Q.Ps.isoTilde (FiniteExtension.completionMap (inducingPlace Q D a) Q.Ps.vTilde x) := by
  let e := intermediateClosureEquiv Q.F T
  exact (A.parentInducingEquiv_apply a (A.localEquiv (inducingField Q D a) x)).trans <|
    (congrArg e (A.localEquiv_apply (inducingField Q D a) x)).trans (e.apply_symm_apply _)

/-- The actual child completion becomes the compositum of the completed base and
the conjugate parent inducing field in the common local closure. -/
theorem parentInducingField_eq [IsGalois Q.E Q.L] (hQ : HasUniquePlaceAbove Q.L Q.Ps.v)
    (hP : Q.Ps.IsCompatible) (τ : Field.absoluteGaloisGroup Q.F.Carrier)
    (σ : FiniteCompletion Q.L Q.Ps.vTilde ≃+* FiniteCompletion Q.L Q.Ps.vTilde)
    (hσ : Continuous σ)
    (hσa : ∀ y : Q.L, σ (algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) y) =
      algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) (a.symm y))
    (hστ : ∀ y, (Q.Ps.isoTilde (σ y) : AlgebraicClosure Q.F.Carrier) =
      τ.symm (Q.Ps.isoTilde y)) :
    A.parentInducingField a = T.field ⊔ (Q.F'.conj τ).field := by
  let := Q.mackeyConjugatePlace_liesUnder a hQ
  have hD := Q.auxiliaryCompletedField_eq hP D (basePlace Q D) T.field A.iso A.commutes
  let e := Proposition48Problem.conjugateInducingEquiv Q a τ hP
  have hA := Q.auxiliaryCompletedField_eq hP (Q.conjugateField a) (Q.mackeyConjugatePlace a)
    (Q.F'.conj τ).field e
      (Proposition48Problem.conjugateInducingEquiv_apply Q a τ hP σ hσ hσa hστ)
  have hM := Q.auxiliaryCompletedField_eq hP (Q.mackeyField D a) (Q.mackeyFinitePlace D a)
    (A.parentInducingField a) ((A.localEquiv (inducingField Q D a)).trans (A.parentInducingEquiv a))
    (A.parentInducingEquiv_localEquiv_apply a)
  calc
    A.parentInducingField a = Q.auxiliaryCompletedField hP (D ⊔ Q.conjugateField a) := hM.symm
    _ = T.field ⊔ (Q.F'.conj τ).field := by
      rw [Q.auxiliaryCompletedField_sup hP hQ, hD, hA]

/-- Identify the inducing field with a specified model of its image in the parent closure. -/
def parentInducingEquivTo (U : Extension Q.F) (hU : A.parentInducingField a = U.field) :
    (A.localInducing a).field ≃+* U.field :=
  (A.parentInducingEquiv a).trans (IntermediateField.equivOfEq hU).toRingEquiv

/-- The actual child place sees the norm-pulled local character under the commuting
identification of the child's inducing completion. -/
theorem place_hasComponent [IsGalois Q.E Q.L] (hQ : HasUniquePlaceAbove Q.L Q.Ps.v)
    (hP : Q.Ps.IsCompatible) (τ : Field.absoluteGaloisGroup Q.F.Carrier)
    (σ : FiniteCompletion Q.L Q.Ps.vTilde ≃+* FiniteCompletion Q.L Q.Ps.vTilde)
    (hσ : Continuous σ)
    (hσa : ∀ y : Q.L, σ (algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) y) =
      algebraMap Q.L (FiniteCompletion Q.L Q.Ps.vTilde) (a.symm y))
    (hστ : ∀ y, (Q.Ps.isoTilde (σ y) : AlgebraicClosure Q.F.Carrier) =
      τ.symm (Q.Ps.isoTilde y))
    (U : Extension Q.F) (hU : A.parentInducingField a = U.field)
    (h : (Q.F'.conj τ).field ≤ U.field) (hχ : Q.Ps.HasComponent Q.ξ Q.χs)
    (η : FieldCharacter (T.asPadicField (p := Q.p)) (A.localInducing a))
    (hη : ∀ y, η y =
      Q.χs (Units.mapEquiv (IntermediateField.equivMap Q.F'.field τ.toAlgHom).symm.toMulEquiv
        ((Q.F'.conj τ).unitsNorm U h
          (Units.mapEquiv (A.parentInducingEquivTo a U hU).toMulEquiv y)))) :
    (A.place a hQ).HasComponent (Q.mackeyCharacter D a) η := by
  let := Q.mackeyConjugatePlace_liesUnder a hQ
  let e : FiniteCompletion (inducingField Q D a) (inducingPlace Q D a) ≃+*
      (A.localInducing a).field := A.localEquiv (inducingField Q D a)
  let eU : FiniteCompletion (Q.mackeyField D a) (Q.mackeyFinitePlace D a) ≃+* U.field :=
    e.trans (A.parentInducingEquivTo a U hU)
  have heU (x : FiniteCompletion (Q.mackeyField D a) (Q.mackeyFinitePlace D a)) :
      (eU x : AlgebraicClosure Q.F.Carrier) =
        Q.Ps.isoTilde (FiniteExtension.completionMap (Q.mackeyFinitePlace D a) Q.Ps.vTilde x) :=
    A.parentInducingEquiv_localEquiv_apply a x
  change ∀ (x : (FiniteCompletion (inducingField Q D a) (inducingPlace Q D a))ˣ)
    (y : (A.localInducing a).fieldˣ), _
  intro x y hy
  have he : Units.mapEquiv e.toMulEquiv x = y := by
    apply Units.ext
    apply Subtype.ext
    let z : FiniteCompletion (inducingField Q D a) (inducingPlace Q D a) := x
    change (A.localEquiv (inducingField Q D a) z : AlgebraicClosure T.field) =
      ((y : (A.localInducing a).field) : AlgebraicClosure T.field)
    exact (A.place_inducing_apply a hQ z).symm.trans hy.symm
  have heUnits : Units.mapEquiv eU.toMulEquiv x =
      Units.mapEquiv (A.parentInducingEquivTo a U hU).toMulEquiv y :=
    calc
      _ = Units.mapEquiv (A.parentInducingEquivTo a U hU).toMulEquiv
          (Units.mapEquiv e.toMulEquiv x) := by
        apply Units.ext
        rfl
      _ = _ := congrArg (Units.mapEquiv (A.parentInducingEquivTo a U hU).toMulEquiv) he
  have hn := Q.mackeyCharacter_finiteComponent_localNorm D a τ hP σ hσ hσa hστ U eU heU h hχ x
  rw [heUnits, ← hη] at hn
  exact hn

end Langlands.Global.Harris.MackeyChild.CompletedBase
