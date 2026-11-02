import Langlands.AbelianScheme.FieldCubePullbackStatement
import Langlands.AbelianScheme.Multiplication
import Langlands.AlgebraicGeometry.Picard.MumfordBundle
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Modules.TensorMonoidal
import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Langlands.CategoryTheory.Picard.Basic
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof

/-! # Pulling the twisted Mumford product bundle back along multiplication on the parameter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.MultiplicationTwist

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.CategoryTheory

/-- The sheafified tensor product of tensor-invertible modules is tensor invertible. -/
lemma tensorObj_tensorInvertible {X : Scheme.{u}} {M N : X.Modules}
    (hM : TensorInvertible M) (hN : TensorInvertible N) :
    TensorInvertible (tensorObj M N) :=
  TensorInvertible.of_iso (localizedTensorIso X M N) (hM.tensor hN)

/-- A line bundle is tensor invertible. -/
lemma lineBundle_tensorInvertible {X : Scheme.{u}} (L : LineBundle X) :
    TensorInvertible L.obj :=
  (locallyFreeRankOneIffTensorInvertible X L.obj).mpr L.property

/-- The pullback of a line bundle is tensor invertible. -/
lemma pullback_tensorInvertible {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) :
    TensorInvertible ((Scheme.Modules.pullback f).obj L.obj) :=
  (locallyFreeRankOneIffTensorInvertible X _).mpr (L.property.pullback f)

/-- The Picard class of a sheafified tensor product is the sum of the classes. -/
lemma ofObject_tensorObj {X : Scheme.{u}} (M N : X.Modules)
    (hM : TensorInvertible M) (hN : TensorInvertible N) (hMN : TensorInvertible (tensorObj M N)) :
    PicardGroup.ofObject (tensorObj M N) hMN =
      PicardGroup.ofObject M hM + PicardGroup.ofObject N hN := by
  rw [← PicardGroup.ofObject_tensor M N hM hN]
  exact (PicardGroup.ofObject_eq_iff _ _ _ _).mpr ⟨(localizedTensorIso X M N).symm⟩

/-- The Picard class of the structure sheaf is zero. -/
lemma ofObject_structureSheaf {X : Scheme.{u}} (h : TensorInvertible (structureSheaf X)) :
    PicardGroup.ofObject (structureSheaf X) h = 0 :=
  PicardGroup.ofObject_unit

/-- Isomorphic tensor-invertible modules have equal Picard classes. -/
lemma ofObject_eq_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (hM : TensorInvertible M) (hN : TensorInvertible N) :
    PicardGroup.ofObject M hM = PicardGroup.ofObject N hN :=
  (PicardGroup.ofObject_eq_iff _ _ _ _).mpr ⟨e⟩

section Classes

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The Picard class, on the self-product `A ×_K A`, of the pullback of a line bundle `L` on `A`
along a morphism `a` over `K`. -/
def pc (L : LineBundle A.X.left) (a : mumfordProduct A ⟶ A.X) :
    PicardGroup (mumfordProduct A).left.Modules :=
  PicardGroup.ofObject ((Scheme.Modules.pullback a.left).obj L.obj)
    (pullback_tensorInvertible a.left L)

/-- The `n`-th tensor power of a line bundle, as a line bundle. -/
def powLB {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) : LineBundle X :=
  ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩

/-- A line bundle pulled back along a constant morphism through a rational point is trivial,
so its class vanishes. -/
lemma pc_one (L : LineBundle A.X.left) : pc A L 1 = 0 := by
  have h1 : ((1 : mumfordProduct A ⟶ A.X)).left =
      (SemiCartesianMonoidalCategory.toUnit (mumfordProduct A)).left ≫ η[A.X].left := by
    rw [Hom.one_def]
    rfl
  obtain ⟨t⟩ := fieldLineBundleTriviality K ((LineBundle.pullback η[A.X].left).obj L)
  let e : (Scheme.Modules.pullback ((1 : mumfordProduct A ⟶ A.X)).left).obj L.obj ≅
      structureSheaf (mumfordProduct A).left :=
    (Scheme.Modules.pullbackCongr h1).app L.obj ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L.obj).symm ≪≫
      (Scheme.Modules.pullback _).mapIso t ≪≫ pullbackUnitIso _
  rw [pc, ofObject_eq_of_iso e _ TensorInvertible.unit]
  exact PicardGroup.ofObject_unit

/-- The class of the pullback of an inverse is the negative class. -/
lemma pc_inverse (L N : LineBundle A.X.left)
    (eN : tensorObj L.obj N.obj ≅ structureSheaf A.X.left) (a : mumfordProduct A ⟶ A.X) :
    pc A N a = - pc A L a := by
  have e : tensorObj ((Scheme.Modules.pullback a.left).obj L.obj)
      ((Scheme.Modules.pullback a.left).obj N.obj) ≅ structureSheaf (mumfordProduct A).left :=
    (pullbackTensorIso a.left L.obj N.obj).symm ≪≫ (Scheme.Modules.pullback a.left).mapIso eN ≪≫
      pullbackUnitIso a.left
  have h := ofObject_eq_of_iso e
    (tensorObj_tensorInvertible (pullback_tensorInvertible a.left L)
      (pullback_tensorInvertible a.left N)) TensorInvertible.unit
  rw [ofObject_tensorObj _ _ (pullback_tensorInvertible a.left L)
    (pullback_tensorInvertible a.left N), ofObject_structureSheaf] at h
  exact eq_neg_of_add_eq_zero_right h

/-- The class of the pullback of a tensor power is the multiple of the class. -/
lemma pc_tensorPow (L : LineBundle A.X.left) (a : mumfordProduct A ⟶ A.X) (n : ℕ) :
    pc A (powLB L n) a = n • pc A L a := by
  induction n with
  | zero =>
    rw [zero_smul]
    exact (ofObject_eq_of_iso (pullbackUnitIso a.left) _ TensorInvertible.unit).trans
      PicardGroup.ofObject_unit
  | succ n ih =>
    have e := ofObject_eq_of_iso (pullbackTensorIso a.left L.obj (tensorPow L.obj n))
      (pullback_tensorInvertible a.left (powLB L (n + 1)))
      (tensorObj_tensorInvertible (pullback_tensorInvertible a.left L)
        (pullback_tensorInvertible a.left (powLB L n)))
    have e2 := e.trans (ofObject_tensorObj ((Scheme.Modules.pullback a.left).obj L.obj)
      ((Scheme.Modules.pullback a.left).obj (tensorPow L.obj n))
      (pullback_tensorInvertible a.left L) (pullback_tensorInvertible a.left (powLB L n)) _)
    change pc A (powLB L (n + 1)) a = pc A L a + pc A (powLB L n) a at e2
    rw [e2, ih, succ_nsmul']

/-- Pulling back further along an endomorphism `Φ` of the self-product. -/
lemma ofObject_pullback_pullback (L : LineBundle A.X.left)
    (Φ : mumfordProduct A ⟶ mumfordProduct A) (a : mumfordProduct A ⟶ A.X)
    (h : TensorInvertible ((Scheme.Modules.pullback Φ.left).obj
      ((Scheme.Modules.pullback a.left).obj L.obj))) :
    PicardGroup.ofObject _ h = pc A L (Φ ≫ a) :=
  ofObject_eq_of_iso ((Scheme.Modules.pullbackComp Φ.left a.left).app L.obj) _ _

/-- The balanced cube identity in the Picard group of the self-product. -/
lemma pc_cube (cube : Langlands.GroupScheme.FieldCubePullbackStatement.{u})
    (L : LineBundle A.X.left) (f g h : mumfordProduct A ⟶ A.X) :
    pc A L (f * g * h) + (pc A L f + (pc A L g + pc A L h)) =
      pc A L (f * g) + (pc A L (f * h) + pc A L (g * h)) := by
  let inv := fun (a : mumfordProduct A ⟶ A.X) => pullback_tensorInvertible a.left L
  have heq := ofObject_eq_of_iso
    (cube K A.toGrp A.smooth A.proper A.geometricallyConnected (mumfordProduct A) f g h L).some
    (tensorObj_tensorInvertible (inv (f * g * h))
      (tensorObj_tensorInvertible (inv f) (tensorObj_tensorInvertible (inv g) (inv h))))
    (tensorObj_tensorInvertible (inv (f * g))
      (tensorObj_tensorInvertible (inv (f * h)) (inv (g * h))))
  rw [ofObject_tensorObj _ _ (inv (f * g * h))
      (tensorObj_tensorInvertible (inv f) (tensorObj_tensorInvertible (inv g) (inv h))),
    ofObject_tensorObj _ _ (inv f) (tensorObj_tensorInvertible (inv g) (inv h)),
    ofObject_tensorObj _ _ (inv g) (inv h),
    ofObject_tensorObj _ _ (inv (f * g)) (tensorObj_tensorInvertible (inv (f * h)) (inv (g * h))),
    ofObject_tensorObj _ _ (inv (f * h)) (inv (g * h))] at heq
  exact heq

/-- The quadratic recursion of the cube identity along multiples of the second coordinate. -/
lemma pc_first_mul_second_pow (cube : Langlands.GroupScheme.FieldCubePullbackStatement.{u})
    (L : LineBundle A.X.left) (j : ℕ) :
    pc A L (mumfordFirst A * mumfordSecond A ^ j) - pc A L (mumfordFirst A) =
      j • (pc A L (mumfordFirst A * mumfordSecond A) - pc A L (mumfordFirst A)) +
        pc A L (mumfordSecond A ^ j) - j • pc A L (mumfordSecond A) := by
  induction j with
  | zero => simp [pc_one]
  | succ j ih =>
    have hc := pc_cube A cube L (mumfordFirst A) (mumfordSecond A ^ j) (mumfordSecond A)
    rw [mul_assoc, ← pow_succ] at hc
    rw [succ_nsmul, succ_nsmul]
    have : pc A L (mumfordFirst A * mumfordSecond A ^ (j + 1)) =
        pc A L (mumfordFirst A * mumfordSecond A ^ j) + pc A L (mumfordFirst A * mumfordSecond A) +
          pc A L (mumfordSecond A ^ (j + 1)) - pc A L (mumfordFirst A) -
            pc A L (mumfordSecond A ^ j) - pc A L (mumfordSecond A) := by
      rw [← sub_eq_zero]
      rw [← sub_eq_zero] at hc
      rw [← hc]
      abel
    rw [this]
    rw [sub_eq_iff_eq_add] at ih
    rw [ih]
    abel

end Classes

section Main

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The twisted Mumford product module `m^* L ⊗ fst^* M` on the self-product `A ×_K A`. -/
abbrev twistedProduct (L M : A.X.left.Modules) : (mumfordProduct A).left.Modules :=
  tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L)
    ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M)

/-- The twisting line-bundle module `[k]^* H ⊗ N_k` on `A`. -/
abbrev multiplicationTwist (H Nk : LineBundle A.X.left) (k : ℕ) : A.X.left.Modules :=
  tensorObj ((Scheme.Modules.pullback (Langlands.GroupScheme.multiplication A.toGrp (k : ℤ)).hom.hom.left).obj H.obj)
    Nk.obj

/-- **The cube identity along multiplication on the second factor.** Let `Φ` be an
endomorphism of `A ×_K A` over `K` with `Φ ≫ fst = fst` and `Φ ≫ snd = snd ^ k`. If `N` is an
inverse of `H` and `Nk` an inverse of `H^k`, then
`Φ^*(m^* H ⊗ fst^* N) ≅ (m^* H^k ⊗ fst^* Nk) ⊗ snd^*([k]^* H ⊗ Nk)`. -/
theorem nonempty_pullback_twistedProduct_iso
    (cube : Langlands.GroupScheme.FieldCubePullbackStatement.{u})
    (H N Nk : LineBundle A.X.left)
    (eN : tensorObj H.obj N.obj ≅ structureSheaf A.X.left) (k : ℕ)
    (eNk : tensorObj (tensorPow H.obj k) Nk.obj ≅ structureSheaf A.X.left)
    (Φ : mumfordProduct A ⟶ mumfordProduct A)
    (h1 : Φ ≫ mumfordFirst A = mumfordFirst A)
    (h2 : Φ ≫ mumfordSecond A = mumfordSecond A ^ k) :
    Nonempty ((Scheme.Modules.pullback Φ.left).obj (twistedProduct A H.obj N.obj) ≅
      tensorObj (twistedProduct A (tensorPow H.obj k) Nk.obj)
        ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj
          (multiplicationTwist A H Nk k))) := by
  let first := mumfordFirst A
  let second := mumfordSecond A
  let mk := (Langlands.GroupScheme.multiplication A.toGrp (k : ℤ)).hom.hom
  have hm : (first * second).left = mumfordAddition A := rfl
  have hfirst : first.left = pullback.fst A.X.hom A.X.hom := rfl
  have hsecond : second.left = pullback.snd A.X.hom A.X.hom := rfl
  have hmk : second ≫ mk = second ^ k := by
    rw [Langlands.GroupScheme.points_multiplication, zpow_natCast]
  -- invertibility certificates
  let iH := fun (a : mumfordProduct A ⟶ A.X) => pullback_tensorInvertible a.left H
  let iN := fun (a : mumfordProduct A ⟶ A.X) => pullback_tensorInvertible a.left N
  let iNk := fun (a : mumfordProduct A ⟶ A.X) => pullback_tensorInvertible a.left Nk
  let iHk := fun (a : mumfordProduct A ⟶ A.X) => pullback_tensorInvertible a.left (powLB H k)
  -- left side
  have iΦH : TensorInvertible ((Scheme.Modules.pullback Φ.left).obj
      ((Scheme.Modules.pullback (mumfordAddition A)).obj H.obj)) :=
    pullback_tensorInvertible Φ.left ((LineBundle.pullback (mumfordAddition A)).obj H)
  have iΦN : TensorInvertible ((Scheme.Modules.pullback Φ.left).obj
      ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj N.obj)) :=
    pullback_tensorInvertible Φ.left ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj N)
  have iL : TensorInvertible ((Scheme.Modules.pullback Φ.left).obj (twistedProduct A H.obj N.obj)) :=
    TensorInvertible.of_iso (pullbackTensorIso Φ.left _ _).symm (tensorObj_tensorInvertible iΦH iΦN)
  have hL : PicardGroup.ofObject _ iL =
      pc A H (first * second ^ k) - pc A H first := by
    have e1 : PicardGroup.ofObject _ iΦH = pc A H (Φ ≫ (first * second)) :=
      ofObject_pullback_pullback A H Φ (first * second) iΦH
    have e2 : PicardGroup.ofObject _ iΦN = pc A N (Φ ≫ first) :=
      ofObject_pullback_pullback A N Φ first iΦN
    rw [ofObject_eq_of_iso (pullbackTensorIso Φ.left _ _) iL (tensorObj_tensorInvertible iΦH iΦN),
      ofObject_tensorObj _ _ iΦH iΦN, e1, e2, MonObj.comp_mul, h1, h2,
      pc_inverse A H N eN first, sub_eq_add_neg]
  -- right side
  have iX : TensorInvertible ((Scheme.Modules.pullback (mumfordAddition A)).obj (tensorPow H.obj k)) :=
    iHk (first * second)
  have iY : TensorInvertible ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj Nk.obj) :=
    iNk first
  have iZ1 : TensorInvertible ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj
      ((Scheme.Modules.pullback mk.left).obj H.obj)) :=
    pullback_tensorInvertible _ ((LineBundle.pullback mk.left).obj H)
  have iZ2 : TensorInvertible ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj Nk.obj) :=
    iNk second
  have iZ : TensorInvertible ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj
      (multiplicationTwist A H Nk k)) :=
    TensorInvertible.of_iso (pullbackTensorIso _ _ _).symm (tensorObj_tensorInvertible iZ1 iZ2)
  have iR : TensorInvertible (tensorObj (twistedProduct A (tensorPow H.obj k) Nk.obj)
      ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj
        (multiplicationTwist A H Nk k))) :=
    tensorObj_tensorInvertible (tensorObj_tensorInvertible iX iY) iZ
  have hZ1 : PicardGroup.ofObject _ iZ1 = pc A H (second ^ k) := by
    rw [← hmk]
    exact ofObject_eq_of_iso ((Scheme.Modules.pullbackComp _ mk.left).app H.obj) _ _
  have hR : PicardGroup.ofObject _ iR =
      k • pc A H (first * second) - k • pc A H first + pc A H (second ^ k) -
        k • pc A H second := by
    rw [ofObject_tensorObj _ _ (tensorObj_tensorInvertible iX iY) iZ,
      ofObject_tensorObj _ _ iX iY,
      ofObject_eq_of_iso (pullbackTensorIso _ _ _) iZ (tensorObj_tensorInvertible iZ1 iZ2),
      ofObject_tensorObj _ _ iZ1 iZ2, hZ1]
    have hX : PicardGroup.ofObject _ iX = k • pc A H (first * second) :=
      pc_tensorPow A H (first * second) k
    have hY : PicardGroup.ofObject _ iY = - (k • pc A H first) :=
      (pc_inverse A (powLB H k) Nk eNk first).trans (by rw [pc_tensorPow])
    have hZ2 : PicardGroup.ofObject _ iZ2 = - (k • pc A H second) :=
      (pc_inverse A (powLB H k) Nk eNk second).trans (by rw [pc_tensorPow])
    rw [hX, hY, hZ2]
    abel
  refine (PicardGroup.ofObject_eq_iff _ _ iL iR).mp ?_
  rw [hL, hR]
  have key := pc_first_mul_second_pow A cube H k
  rw [key, nsmul_sub]

/-- Anchor proposition of this module (internal): given the balanced cube identity, for every
abelian scheme over a field, line bundles `H`, `N`, `Nk` with `H ⊗ N ≅ 𝒪` and `H^k ⊗ Nk ≅ 𝒪`, and
every endomorphism `Φ` of `A ×_K A` with `Φ ≫ fst = fst` and `Φ ≫ snd = snd ^ k`,
`Φ^*(m^* H ⊗ fst^* N) ≅ (m^* H^k ⊗ fst^* Nk) ⊗ snd^*([k]^* H ⊗ Nk)`. -/
def MumfordProductMultiplicationTwistStatement : Prop :=
  Langlands.GroupScheme.FieldCubePullbackStatement.{u} →
  ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (H N Nk : LineBundle A.X.left),
    Nonempty (tensorObj H.obj N.obj ≅ structureSheaf A.X.left) →
    ∀ k : ℕ, Nonempty (tensorObj (tensorPow H.obj k) Nk.obj ≅ structureSheaf A.X.left) →
    ∀ Φ : mumfordProduct A ⟶ mumfordProduct A,
      Φ ≫ mumfordFirst A = mumfordFirst A → Φ ≫ mumfordSecond A = mumfordSecond A ^ k →
      Nonempty ((Scheme.Modules.pullback Φ.left).obj (twistedProduct A H.obj N.obj) ≅
        tensorObj (twistedProduct A (tensorPow H.obj k) Nk.obj)
          ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj
            (multiplicationTwist A H Nk k)))

/-- The anchor proposition holds. -/
theorem mumfordProductMultiplicationTwist : MumfordProductMultiplicationTwistStatement.{u} :=
  fun cube _ _ A H N Nk ⟨eN⟩ k ⟨eNk⟩ Φ h1 h2 =>
    nonempty_pullback_twistedProduct_iso A cube H N Nk eN k eNk Φ h1 h2

end Main

end Langlands.AbelianScheme.MultiplicationTwist
