import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChangeNormalization

/-! # Fixed-frame test comparisons defined directly by coefficient maps -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}

/-- Equal underlying coefficient maps and equal scalars retain an actual identity formal comparison. -/
def mapReAlgebraIso (E : OrderAction D M) {S : Type v} [CommRing S]
    (α β : Algebra O S) (e : α = β)
    (f : (letI := α; R →ₐ[O] S)) (g : (letI := β; R →ₐ[O] S))
    (hf : (letI := α; f.toRingHom) = (letI := β; g.toRingHom)) :
    (letI := β; Iso ((letI := α; E.map f).reAlgebra β e) (E.map g)) := by
  cases e
  have hfg : f = g := AlgHom.ext (fun x => RingHom.congr_fun hf x)
  cases hfg
  exact Iso.refl _

/-- The actual forward comparison has identity series. -/
theorem mapReAlgebraIso_hom_coordinates (E : OrderAction D M) {S : Type v} [CommRing S]
    (α β : Algebra O S) (e : α = β)
    (f : (letI := α; R →ₐ[O] S)) (g : (letI := β; R →ₐ[O] S))
    (hf : (letI := α; f.toRingHom) = (letI := β; g.toRingHom)) :
    (letI := β; (mapReAlgebraIso E α β e f g hf).hom.val.toHom.toCoordinateMap) =
      CoordinateMap.id := by
  cases e
  have hfg : f = g := AlgHom.ext (fun x => RingHom.congr_fun hf x)
  cases hfg
  rfl

/-- The actual inverse comparison also has identity series. -/
theorem mapReAlgebraIso_inv_coordinates (E : OrderAction D M) {S : Type v} [CommRing S]
    (α β : Algebra O S) (e : α = β)
    (f : (letI := α; R →ₐ[O] S)) (g : (letI := β; R →ₐ[O] S))
    (hf : (letI := α; f.toRingHom) = (letI := β; g.toRingHom)) :
    (letI := β; (mapReAlgebraIso E α β e f g hf).inv.val.toHom.toCoordinateMap) =
      CoordinateMap.id := by
  cases e
  have hfg : f = g := AlgHom.ext (fun x => RingHom.congr_fun hf x)
  cases hfg
  rfl

/-- The actual forward scalar-composition comparison has identity series. -/
theorem mapCompIso_hom_coordinates (E : OrderAction D M)
    {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (E.mapCompIso f g).hom.val.toHom.toCoordinateMap = CoordinateMap.id := rfl

/-- The actual inverse scalar-composition comparison has identity series. -/
theorem mapCompIso_inv_coordinates (E : OrderAction D M)
    {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    (E.mapCompIso f g).inv.val.toHom.toCoordinateMap = CoordinateMap.id := rfl

/-- Scalar retyping retains the complete forward identity series of coefficient composition. -/
theorem mapCompIso_reAlgebra_hom_coordinates (E : OrderAction D M)
    {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [αT : Algebra O T]
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (β : Algebra O T) (e : αT = β) :
    (letI := β; ((letI := αT; E.mapCompIso f g).reAlgebra β e).hom.val.toHom.toCoordinateMap) =
      CoordinateMap.id := by
  cases e
  rfl

/-- Scalar retyping retains the complete inverse identity series of coefficient composition. -/
theorem mapCompIso_reAlgebra_inv_coordinates (E : OrderAction D M)
    {S T : Type v} [CommRing S] [CommRing T] [Algebra O S] [αT : Algebra O T]
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) (β : Algebra O T) (e : αT = β) :
    (letI := β; ((letI := αT; E.mapCompIso f g).reAlgebra β e).inv.val.toHom.toCoordinateMap) =
      CoordinateMap.id := by
  cases e
  rfl

section Composition

variable {N P : ModuleLaw O R σ}
variable {E : OrderAction D M} {E' : OrderAction D N} {E'' : OrderAction D P}

/-- Composition retains complete forward identity series. -/
theorem Iso.trans_hom_coordinates_id (f : Iso E E') (g : Iso E' E'')
    (hf : f.hom.val.toHom.toCoordinateMap = CoordinateMap.id)
    (hg : g.hom.val.toHom.toCoordinateMap = CoordinateMap.id) :
    (f.trans g).hom.val.toHom.toCoordinateMap = CoordinateMap.id := by
  change g.hom.val.toHom.toCoordinateMap.comp f.hom.val.toHom.toCoordinateMap = _
  rw [hf, hg]
  exact CoordinateMap.id_comp _

/-- Composition retains complete inverse identity series. -/
theorem Iso.trans_inv_coordinates_id (f : Iso E E') (g : Iso E' E'')
    (hf : f.inv.val.toHom.toCoordinateMap = CoordinateMap.id)
    (hg : g.inv.val.toHom.toCoordinateMap = CoordinateMap.id) :
    (f.trans g).inv.val.toHom.toCoordinateMap = CoordinateMap.id := by
  change f.inv.val.toHom.toCoordinateMap.comp g.inv.val.toHom.toCoordinateMap = _
  rw [hf, hg]
  exact CoordinateMap.id_comp _

end Composition

section ScalarTransport

variable {T : Type v} [CommRing T] {α : Algebra O T}
variable {M' N' : (letI := α; ModuleLaw O T σ)}
variable {E : (letI := α; OrderAction D M')}
variable {E' : (letI := α; OrderAction D N')}

/-- Scalar equality transport retains the complete forward formal coordinate map. -/
theorem Iso.reAlgebra_hom_coordinates (f : (letI := α; Iso E E'))
    (β : Algebra O T) (e : α = β) :
    (letI := β; (f.reAlgebra β e).hom.val.toHom.toCoordinateMap) =
      (letI := α; f.hom.val.toHom.toCoordinateMap) := by
  cases e
  rfl

/-- Scalar equality transport retains the complete inverse formal coordinate map. -/
theorem Iso.reAlgebra_inv_coordinates (f : (letI := α; Iso E E'))
    (β : Algebra O T) (e : α = β) :
    (letI := β; (f.reAlgebra β e).inv.val.toHom.toCoordinateMap) =
      (letI := α; f.inv.val.toHom.toCoordinateMap) := by
  cases e
  rfl

end ScalarTransport

end Langlands.FormalGroup.ModuleLaw.OrderAction

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- The fixed-frame test comparison uses only the actual scalar maps and no target chart. -/
def baseChangeGlobalFrameTestIso (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let δ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) T
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC : δ = γ := BasicAtlas.coefficientAlgebra_comp_transport
    (BasicAtlas.coefficientTest φ) C _ (BasicAtlas.coefficientAlgebraAlong_eq φ)
  let oldMap := (letI := δ;
    (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj T).comp X.residueMap)
  letI := γ
  let newMap := (IsScalarTower.toAlgHom 𝒪[K]
    ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C).comp
      (φ.comp X.residueMap)
  let hm : (letI := δ; oldMap.toRingHom) = (letI := γ; newMap.toRingHom) := by ext x; rfl
  let jnew := Φ.val.order.mapCompIso (φ.comp X.residueMap)
    (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C)
  let jmid := ModuleLaw.OrderAction.mapReAlgebraIso Φ.val.order δ γ eC oldMap newMap hm
  let jold := (letI := δ;
    (Φ.val.order.mapCompIso X.residueMap
      (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj T)).reAlgebra γ eC)
  ModuleLaw.OrderAction.Iso.trans (O := 𝒪[K]) (R := C) jnew
    (ModuleLaw.OrderAction.Iso.trans (O := 𝒪[K]) (R := C)
      (ModuleLaw.OrderAction.Iso.symm (O := 𝒪[K]) (R := C) jmid)
      (ModuleLaw.OrderAction.Iso.symm (O := 𝒪[K]) (R := C) jold))

set_option backward.isDefEq.respectTransparency false in
/-- The direct fixed-frame comparison has complete forward identity series. -/
theorem baseChangeGlobalFrameTestIso_hom_coordinates (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj) :
    (X.baseChangeGlobalFrameTestIso f C).hom.val.toHom.toCoordinateMap = CoordinateMap.id := by
  unfold baseChangeGlobalFrameTestIso
  apply ModuleLaw.OrderAction.Iso.trans_hom_coordinates_id
  · exact ModuleLaw.OrderAction.mapCompIso_hom_coordinates _ _ _
  · apply ModuleLaw.OrderAction.Iso.trans_hom_coordinates_id
    · exact ModuleLaw.OrderAction.mapReAlgebraIso_inv_coordinates _ _ _ _ _ _ _
    · exact ModuleLaw.OrderAction.mapCompIso_reAlgebra_inv_coordinates
        (αT := coefficientAlgebra (O := 𝒪[K])
          (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C)) _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Its actual inverse has complete identity series as well. -/
theorem baseChangeGlobalFrameTestIso_inv_coordinates (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj) :
    (X.baseChangeGlobalFrameTestIso f C).inv.val.toHom.toCoordinateMap = CoordinateMap.id := by
  unfold baseChangeGlobalFrameTestIso
  apply ModuleLaw.OrderAction.Iso.trans_inv_coordinates_id
  · exact ModuleLaw.OrderAction.mapCompIso_inv_coordinates _ _ _
  · apply ModuleLaw.OrderAction.Iso.trans_inv_coordinates_id
    · exact ModuleLaw.OrderAction.mapReAlgebraIso_hom_coordinates _ _ _ _ _ _ _
    · exact ModuleLaw.OrderAction.mapCompIso_reAlgebra_hom_coordinates
        (αT := coefficientAlgebra (O := 𝒪[K])
          (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C)) _ _ _ _ _

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
