import Langlands.Geometry.FormalGroup.ScalarTorsionPolarization
import Langlands.Geometry.FormalGroup.ScalarTorsionSchemeBaseChange
import Langlands.GroupScheme.Cartier.CharacterBaseChangeNaturality

/-! # Base change of principal polarizations on scalar-power kernels -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite _root_.AlgebraicGeometry
open Langlands.GroupScheme Langlands.Shimura Hom.FiniteKernelModel
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}
variable (φ : R →ₐ[O] S)

namespace IsPiDivisible

variable (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
variable {T T' : Over (Spec (CommRingCat.of S))}

private def groupIsoOfCommIso {B : Scheme.{v}} {G H : CommGroupScheme B} (e : G ≅ H) :
    G.toGrp ≅ H.toGrp where
  hom := e.hom.toMul
  inv := e.inv.toMul
  hom_inv_id := congrArg Additive.toMul e.hom_inv_id
  inv_hom_id := congrArg Additive.toMul e.inv_hom_id

/-- The points of the extended torsion scheme are the original kernel points
on the test regarded over the original base. -/
def torsionPointBaseChangeEquiv (n : ℕ) (T : Over (Spec (CommRingCat.of S))) :
    (T ⟶ ((hM.map φ).torsionSchemeInclusions.obj n).X) ≃*
      ((Over.map (coefficientSpecMap φ)).obj T ⟶ (hM.torsionSchemeInclusions.obj n).X) :=
  (GroupScheme.isoPointsEquiv
    (groupIsoOfCommIso (hM.torsionPullbackIso φ n)) T).trans
    (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ)
      (hM.torsionSchemeInclusions.obj n).toGrp T)

theorem torsionPointBaseChangeEquiv_naturality (n : ℕ) (a : T' ⟶ T)
    (x : T ⟶ ((hM.map φ).torsionSchemeInclusions.obj n).X) :
    hM.torsionPointBaseChangeEquiv φ n T' (a ≫ x) =
      (Over.map (coefficientSpecMap φ)).map a ≫ hM.torsionPointBaseChangeEquiv φ n T x := by
  change GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ)
      (hM.torsionSchemeInclusions.obj n).toGrp T'
        ((a ≫ x) ≫ (hM.torsionPullbackIso φ n).hom.toMul.hom.hom) = _
  exact (congrArg (GroupScheme.baseChangePointsEquiv (coefficientSpecMap φ)
    (hM.torsionSchemeInclusions.obj n).toGrp T') (Category.assoc a x _)).trans
    (GroupScheme.baseChangePointsEquiv_naturality (coefficientSpecMap φ)
      (hM.torsionSchemeInclusions.obj n).toGrp a
        (x ≫ (hM.torsionPullbackIso φ n).hom.toMul.hom.hom))

theorem torsionPointBaseChangeEquiv_map {m n : ℕ}
    (f : hM.torsionSchemeInclusions.obj m ⟶ hN.torsionSchemeInclusions.obj n)
    (f' : (hM.map φ).torsionSchemeInclusions.obj m ⟶ (hN.map φ).torsionSchemeInclusions.obj n)
    (hf : f' ≫ (hN.torsionPullbackIso φ n).hom = (hM.torsionPullbackIso φ m).hom ≫
      (CommGroupScheme.baseChange (coefficientSpecMap φ)).map f)
    (x : T ⟶ ((hM.map φ).torsionSchemeInclusions.obj m).X) :
    hN.torsionPointBaseChangeEquiv φ n T (x ≫ f'.toMul.hom.hom) =
      hM.torsionPointBaseChangeEquiv φ m T x ≫ f.toMul.hom.hom := by
  let b := coefficientSpecMap φ
  let G := hN.torsionSchemeInclusions.obj n
  have h := congrArg (fun k => k.toMul.hom.hom) hf
  change f'.toMul.hom.hom ≫ (hN.torsionPullbackIso φ n).hom.toMul.hom.hom =
    (hM.torsionPullbackIso φ m).hom.toMul.hom.hom ≫
      ((CommGroupScheme.baseChange b).map f).toMul.hom.hom at h
  change GroupScheme.baseChangePointsEquiv b G.toGrp T
    ((x ≫ f'.toMul.hom.hom) ≫ (hN.torsionPullbackIso φ n).hom.toMul.hom.hom) = _
  have hp := (Category.assoc x f'.toMul.hom.hom _).trans
    ((congrArg (x ≫ ·) h).trans
      (Category.assoc x (hM.torsionPullbackIso φ m).hom.toMul.hom.hom _).symm)
  exact (congrArg (GroupScheme.baseChangePointsEquiv b G.toGrp T) hp).trans
    (GroupScheme.baseChangePointsEquiv_comp b f.toMul T
      (x ≫ (hM.torsionPullbackIso φ m).hom.toMul.hom.hom))

/-- The same comparison on the additive point presheaves. -/
def torsionPointBaseChangeIso (n : ℕ) :
    additivePoints ((hM.map φ).torsionSchemeInclusions.obj n).toGrp ≅
      (Over.map (coefficientSpecMap φ)).op ⋙ additivePoints (hM.torsionSchemeInclusions.obj n).toGrp :=
  NatIso.ofComponents
    (fun T => (hM.torsionPointBaseChangeEquiv φ n T.unop).toAdditive.toAddCommGrpIso)
    (fun a => by
      ext x
      exact hM.torsionPointBaseChangeEquiv_naturality φ n a.unop x.toMul)

/-- Relative characters of the original and extended kernel schemes agree on the
corresponding tests. -/
def torsionCharactersBaseChangeIso (n : ℕ) :
    (Over.map (coefficientSpecMap φ)).op ⋙ hM.torsionCharacters n ≅ (hM.map φ).torsionCharacters n :=
  Cartier.charactersBaseChangeIso (hM.torsionSchemeInclusions.obj n) (coefficientSpecMap φ) ≪≫
    (Cartier.relativeHomBifunctor (Gm (Spec (CommRingCat.of S)))).mapIso
      (hM.torsionPullbackIso φ n).op

set_option maxHeartbeats 800000 in
theorem torsionCharactersBaseChangeIso_precompose {m n : ℕ}
    (f : hM.torsionSchemeInclusions.obj m ⟶ hN.torsionSchemeInclusions.obj n)
    (f' : (hM.map φ).torsionSchemeInclusions.obj m ⟶ (hN.map φ).torsionSchemeInclusions.obj n)
    (hf : f' ≫ (hN.torsionPullbackIso φ n).hom = (hM.torsionPullbackIso φ m).hom ≫
      (CommGroupScheme.baseChange (coefficientSpecMap φ)).map f)
    (χ : (hN.torsionCharacters n).obj (op ((Over.map (coefficientSpecMap φ)).obj T))) :
    (hM.torsionCharactersBaseChangeIso φ m).hom.app (op T)
        (Cartier.precompose (Gm (Spec (CommRingCat.of R))) f ((Over.map (coefficientSpecMap φ)).obj T) χ) =
      Cartier.precompose (Gm (Spec (CommRingCat.of S))) f' T
        ((hN.torsionCharactersBaseChangeIso φ n).hom.app (op T) χ) := by
  let b := coefficientSpecMap φ
  let H := Gm (Spec (CommRingCat.of S))
  let G := Gm (Spec (CommRingCat.of R))
  let eM := (hM.torsionPullbackIso φ m).hom
  let eN := (hN.torsionPullbackIso φ n).hom
  let χ' := (Cartier.charactersBaseChangeIso (hN.torsionSchemeInclusions.obj n) b).hom.app (op T) χ
  change Cartier.precompose H eM T
      ((Cartier.charactersBaseChangeIso (hM.torsionSchemeInclusions.obj m) b).hom.app (op T)
        (Cartier.precompose G f ((Over.map b).obj T) χ)) =
    Cartier.precompose H f' T (Cartier.precompose H eN T χ')
  have h := Cartier.charactersBaseChangeIso_precompose b T f χ
  exact (congrArg (Cartier.precompose H eM T) h).trans
    ((Cartier.precompose_comp H eM ((CommGroupScheme.baseChange b).map f) T χ').symm.trans
      ((congrArg (fun k => Cartier.precompose H k T χ') hf.symm).trans
        (Cartier.precompose_comp H f' eN T χ')))

theorem torsionCharactersBaseChangeIso_evaluation (n : ℕ)
    (χ : (hM.torsionCharacters n).obj (op ((Over.map (coefficientSpecMap φ)).obj T)))
    (x : T ⟶ ((hM.map φ).torsionSchemeInclusions.obj n).X) :
    Gm.pointsEquiv (Spec (CommRingCat.of S)) T
        (Cartier.evaluation ((hM.torsionCharactersBaseChangeIso φ n).hom.app (op T) χ) x) =
      Gm.pointsEquiv (Spec (CommRingCat.of R)) ((Over.map (coefficientSpecMap φ)).obj T)
        (Cartier.evaluation χ (hM.torsionPointBaseChangeEquiv φ n T x)) := by
  let b := coefficientSpecMap φ
  let e := (hM.torsionPullbackIso φ n).hom
  let χ' := (Cartier.charactersBaseChangeIso (hM.torsionSchemeInclusions.obj n) b).hom.app (op T) χ
  change Gm.pointsEquiv (Spec (CommRingCat.of S)) T
      (Cartier.evaluation ((CommGroupScheme.baseChange T.hom).map e ≫ χ') x) = _
  exact (congrArg (Gm.pointsEquiv (Spec (CommRingCat.of S)) T)
    (Cartier.evaluation_precompose e χ' x)).trans
    (Cartier.charactersBaseChangeIso_evaluation b T (hM.torsionSchemeInclusions.obj n)
      χ (x ≫ e.toMul.hom.hom))

end IsPiDivisible

namespace TorsionCartierDuality

variable {hM : M.IsPiDivisible π} {hN : N.IsPiDivisible π}
variable (duality : TorsionCartierDuality hM hN)

private def baseChangeLevel (n : ℕ) :
    additivePoints ((hM.map φ).torsionSchemeInclusions.obj n).toGrp ≅
      (hN.map φ).torsionCharacters n :=
  hM.torsionPointBaseChangeIso φ n ≪≫
    Functor.isoWhiskerLeft (Over.map (coefficientSpecMap φ)).op (duality.level n) ≪≫
    hN.torsionCharactersBaseChangeIso φ n

set_option maxHeartbeats 800000 in
/-- Extend the coherent torsion duality to any coefficient algebra. -/
def baseChange : TorsionCartierDuality (hM.map φ) (hN.map φ) where
  level := duality.baseChangeLevel φ
  inclusion {m n} i T x := by
    let T₀ := (Over.map (coefficientSpecMap φ)).obj T
    let G := Gm (Spec (CommRingCat.of R))
    let H := Gm (Spec (CommRingCat.of S))
    let x₀ := hM.torsionPointBaseChangeEquiv φ m T x
    let incl := hM.torsionSchemeInclusions.map i
    let incl' := (hM.map φ).torsionSchemeInclusions.map i
    let trans := hN.torsionSchemeTower.map i.op
    let trans' := (hN.map φ).torsionSchemeTower.map i.op
    let character (j : ℕ) (y : T₀ ⟶ (hM.torsionSchemeInclusions.obj j).X) :=
      (duality.level j).hom.app (op T₀) (Additive.ofMul y)
    let convertCharacter (j : ℕ) (χ : (hN.torsionCharacters j).obj (op T₀)) :=
      (hN.torsionCharactersBaseChangeIso φ j).hom.app (op T) χ
    change convertCharacter n
        (character n (hM.torsionPointBaseChangeEquiv φ n T (x ≫ incl'.toMul.hom.hom))) =
      Cartier.precompose H trans' T (convertCharacter m (character m x₀))
    have hp := hM.torsionPointBaseChangeEquiv_map φ hM incl incl'
      (hM.torsionPullbackIso_inclusion φ i) x
    have hc : character n (x₀ ≫ incl.toMul.hom.hom) =
        Cartier.precompose G trans T₀ (character m x₀) :=
      duality.inclusion i T₀ x₀
    exact (congrArg (fun y => convertCharacter n (character n y)) hp).trans
      ((congrArg (convertCharacter n) hc).trans
        (hN.torsionCharactersBaseChangeIso_precompose φ hN trans trans'
          (hN.torsionPullbackIso_transition φ i) (character m x₀)))

/-- The extended pairing gives the same unit on the corresponding test. -/
theorem baseChange_pairing (n : ℕ) (T : Over (Spec (CommRingCat.of S)))
    (x : T ⟶ ((hM.map φ).torsionSchemeInclusions.obj n).X)
    (y : T ⟶ ((hN.map φ).torsionSchemeInclusions.obj n).X) :
    Gm.pointsEquiv (Spec (CommRingCat.of S)) T ((duality.baseChange φ).pairing n x y) =
      Gm.pointsEquiv (Spec (CommRingCat.of R)) ((Over.map (coefficientSpecMap φ)).obj T)
        (duality.pairing n (hM.torsionPointBaseChangeEquiv φ n T x)
          (hN.torsionPointBaseChangeEquiv φ n T y)) :=
  hN.torsionCharactersBaseChangeIso_evaluation φ n
    ((duality.level n).hom.app (op ((Over.map (coefficientSpecMap φ)).obj T))
      (Additive.ofMul (hM.torsionPointBaseChangeEquiv φ n T x))) y

end TorsionCartierDuality

namespace TorsionPrincipalPolarization

variable {hM : M.IsPiDivisible π}

set_option maxHeartbeats 800000 in
/-- Principal polarizations base-change as the actual skew Cartier self-dualities. -/
def baseChange (polarization : TorsionPrincipalPolarization hM) :
    TorsionPrincipalPolarization (hM.map φ) where
  toTorsionCartierDuality := polarization.toTorsionCartierDuality.baseChange φ
  skew n T x y := by
    let T₀ := (Over.map (coefficientSpecMap φ)).obj T
    let x₀ := hM.torsionPointBaseChangeEquiv φ n T x
    let y₀ := hM.torsionPointBaseChangeEquiv φ n T y
    let oldEquiv := Gm.pointsEquiv (Spec (CommRingCat.of R)) T₀
    let newEquiv := Gm.pointsEquiv (Spec (CommRingCat.of S)) T
    let duality := polarization.toTorsionCartierDuality
    apply newEquiv.injective
    exact (duality.baseChange_pairing φ n T x y).trans
      ((congrArg oldEquiv (polarization.skew n T₀ x₀ y₀)).trans
        ((map_inv oldEquiv (duality.pairing n y₀ x₀)).trans
          ((congrArg Inv.inv (duality.baseChange_pairing φ n T y x).symm).trans
            (map_inv newEquiv ((duality.baseChange φ).pairing n y x)).symm)))

end TorsionPrincipalPolarization

namespace OrderAction

variable {A : Type w} [Ring A] [Algebra O A]
variable {E : OrderAction A M} {hM : M.IsPiDivisible π}
variable {star : AlgebraInvolution O A} {polarization : TorsionPrincipalPolarization hM}

set_option maxHeartbeats 800000 in
/-- The full order adjointness relation survives coefficient extension. -/
theorem IsAntilinearTorsionPolarization.baseChange
    (hpolarization : E.IsAntilinearTorsionPolarization star polarization) :
    (E.map φ).IsAntilinearTorsionPolarization star (polarization.baseChange φ) := by
  intro a n T x
  let f := (E.action a).scalarTorsionSchemeMap hM hM n
  let f' := ((E.map φ).action a).scalarTorsionSchemeMap (hM.map φ) (hM.map φ) n
  let g := (E.action (star a)).scalarTorsionSchemeMap hM hM n
  let g' := ((E.map φ).action (star a)).scalarTorsionSchemeMap (hM.map φ) (hM.map φ) n
  let G := Gm (Spec (CommRingCat.of R))
  let H := Gm (Spec (CommRingCat.of S))
  let T₀ := (Over.map (coefficientSpecMap φ)).obj T
  let x₀ := hM.torsionPointBaseChangeEquiv φ n T x
  let character (y : T₀ ⟶ (hM.torsionSchemeInclusions.obj n).X) :=
    (polarization.level n).hom.app (op T₀) (Additive.ofMul y)
  let convertCharacter (χ : (hM.torsionCharacters n).obj (op T₀)) :=
    (hM.torsionCharactersBaseChangeIso φ n).hom.app (op T) χ
  change convertCharacter
      (character (hM.torsionPointBaseChangeEquiv φ n T (x ≫ f'.toMul.hom.hom))) =
    Cartier.precompose H g' T (convertCharacter (character x₀))
  have hp := hM.torsionPointBaseChangeEquiv_map φ hM f f'
    (hM.torsionPullbackIso_naturality φ hM (E.action a) n) x
  have hc : character (x₀ ≫ f.toMul.hom.hom) = Cartier.precompose G g T₀ (character x₀) :=
    hpolarization a n T₀ x₀
  exact (congrArg (fun y => convertCharacter (character y)) hp).trans
    ((congrArg convertCharacter hc).trans (hM.torsionCharactersBaseChangeIso_precompose φ hM g g'
      (hM.torsionPullbackIso_naturality φ hM (E.action (star a)) n) (character x₀)))

end OrderAction

end Langlands.FormalGroup.ModuleLaw
