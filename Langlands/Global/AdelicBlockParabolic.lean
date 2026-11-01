import Langlands.Group.GL.Blocks
import Langlands.Global.AdelicGL

/-!
# Block parabolics over actual number-field adeles

The finite/infinite splitting restricts to the actual block parabolic and
commutes with its actual Levi projection and block diagonal section.
-/

noncomputable section

universe uF

namespace Langlands.Global.AdelicBlockParabolic

open NumberField IsDedekindDomain
open Langlands.GeneralLinear

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

/-- Rational points of the actual upper block parabolic. No topology is chosen on `F`. -/
abbrev Rational := ↥(B.parabolic F)

/-- Full adelic points, with the actual matrix subgroup topology. -/
abbrev Full := ↥(B.parabolic (AdeleRing (𝓞 F) F))

/-- Finite adelic points, over the actual restricted-product coefficient ring. -/
abbrev Finite := ↥(B.parabolic (FiniteAdeleRing (𝓞 F) F))

/-- Archimedean points, over the product of the archimedean completions. -/
abbrev Infinite := ↥(B.parabolic (InfiniteAdeleRing F))

/-- The rational diagonal map restricted to the actual block parabolic. -/
def rational : Rational F B →* Full F B where
  toFun g := ⟨AdelicGL.rational F n g.val, by
    apply (B.mem_parabolic_iff _ _).mpr
    intro i j a b hij
    change algebraMap F (AdeleRing (𝓞 F) F)
      (g.val (B.index i a) (B.index j b)) = 0
    rw [(B.mem_parabolic_iff _ _).mp g.property i j a b hij, map_zero]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

theorem rational_injective : Function.Injective (rational F B) := by
  intro g h he
  apply Subtype.ext
  exact AdelicGL.rational_injective F n (congrArg Subtype.val he)

private def infiniteHom : Full F B →* Infinite F B where
  toFun g := ⟨AdelicGL.infinite F n g.val, by
    apply (B.mem_parabolic_iff _ _).mpr
    intro i j a b hij
    exact congrArg Prod.fst ((B.mem_parabolic_iff _ _).mp g.property i j a b hij)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

private def finiteHom : Full F B →* Finite F B where
  toFun g := ⟨AdelicGL.finite F n g.val, by
    apply (B.mem_parabolic_iff _ _).mpr
    intro i j a b hij
    exact congrArg Prod.snd ((B.mem_parabolic_iff _ _).mp g.property i j a b hij)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

/-- The archimedean projection restricted to the actual parabolic. -/
def infinite : Full F B →ₜ* Infinite F B where
  toMonoidHom := infiniteHom F B
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (AdelicGL.infinite F n).continuous.comp continuous_subtype_val

/-- The finite projection restricted to the actual parabolic. -/
def finite : Full F B →ₜ* Finite F B where
  toMonoidHom := finiteHom F B
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (AdelicGL.finite F n).continuous.comp continuous_subtype_val

@[simp] theorem infinite_val (g : Full F B) :
    (infinite F B g).val = AdelicGL.infinite F n g.val := rfl

@[simp] theorem finite_val (g : Full F B) :
    (finite F B g).val = AdelicGL.finite F n g.val := rfl

/-- Pair actual archimedean and finite parabolic matrices and their inverses. -/
def pair (a : Infinite F B) (b : Finite F B) : Full F B :=
  ⟨AdelicGL.pair F n a.val b.val, by
    apply (B.mem_parabolic_iff _ _).mpr
    intro i j x y hij
    apply Prod.ext
    · exact (B.mem_parabolic_iff _ _).mp a.property i j x y hij
    · exact (B.mem_parabolic_iff _ _).mp b.property i j x y hij⟩

@[simp] theorem pair_val (a : Infinite F B) (b : Finite F B) :
    (pair F B a b).val = AdelicGL.pair F n a.val b.val := rfl

@[simp] theorem infinite_pair (a : Infinite F B) (b : Finite F B) :
    infinite F B (pair F B a b) = a :=
  Subtype.ext (AdelicGL.infinite_pair F n a.val b.val)

@[simp] theorem finite_pair (a : Infinite F B) (b : Finite F B) :
    finite F B (pair F B a b) = b :=
  Subtype.ext (AdelicGL.finite_pair F n a.val b.val)

@[simp] theorem pair_projections (g : Full F B) :
    pair F B (infinite F B g) (finite F B g) = g :=
  Subtype.ext (AdelicGL.pair_projections F n g.val)

theorem continuous_pair :
    Continuous (fun p : Infinite F B × Finite F B => pair F B p.1 p.2) :=
  ((AdelicGL.continuous_pair F n).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- The genuine multiplicative homeomorphism of full parabolic points with the two factors. -/
def split : Full F B ≃ₜ* Infinite F B × Finite F B where
  toFun g := (infinite F B g, finite F B g)
  invFun p := pair F B p.1 p.2
  left_inv := pair_projections F B
  right_inv p := Prod.ext (infinite_pair F B p.1 p.2) (finite_pair F B p.1 p.2)
  map_mul' g h := Prod.ext ((infinite F B).map_mul g h) ((finite F B).map_mul g h)
  continuous_toFun := (infinite F B).continuous.prodMk (finite F B).continuous
  continuous_invFun := continuous_pair F B

/-- Include the archimedean parabolic, with identity in the finite factor. -/
def ofInfinite : Infinite F B →ₜ* Full F B :=
  (ContinuousMonoidHom.toContinuousMonoidHom (split F B).symm).comp
    (ContinuousMonoidHom.inl _ _)

/-- Include the finite parabolic, with identity in the archimedean factor. -/
def ofFinite : Finite F B →ₜ* Full F B :=
  (ContinuousMonoidHom.toContinuousMonoidHom (split F B).symm).comp
    (ContinuousMonoidHom.inr _ _)

/-- The actual product of full adelic block general linear groups. -/
abbrev FullLevi := B.Levi (AdeleRing (𝓞 F) F)

/-- The actual product of finite adelic block general linear groups. -/
abbrev FiniteLevi := B.Levi (FiniteAdeleRing (𝓞 F) F)

/-- The actual product of archimedean block general linear groups. -/
abbrev InfiniteLevi := B.Levi (InfiniteAdeleRing F)

/-- Project each actual Levi block to the archimedean coefficient ring. -/
def leviInfinite : FullLevi F B →ₜ* InfiniteLevi F B where
  toFun m i := AdelicGL.infinite F (B.size i) (m i)
  map_one' := funext fun i => map_one (AdelicGL.infinite F (B.size i))
  map_mul' m k := funext fun i => map_mul (AdelicGL.infinite F (B.size i)) (m i) (k i)
  continuous_toFun := continuous_pi fun i =>
    (AdelicGL.infinite F (B.size i)).continuous.comp (continuous_apply i)

/-- Project each actual Levi block to the finite coefficient ring. -/
def leviFinite : FullLevi F B →ₜ* FiniteLevi F B where
  toFun m i := AdelicGL.finite F (B.size i) (m i)
  map_one' := funext fun i => map_one (AdelicGL.finite F (B.size i))
  map_mul' m k := funext fun i => map_mul (AdelicGL.finite F (B.size i)) (m i) (k i)
  continuous_toFun := continuous_pi fun i =>
    (AdelicGL.finite F (B.size i)).continuous.comp (continuous_apply i)

/-- Pair each pair of actual archimedean and finite invertible Levi blocks. -/
def leviPair (a : InfiniteLevi F B) (b : FiniteLevi F B) : FullLevi F B :=
  fun i => AdelicGL.pair F (B.size i) (a i) (b i)

@[simp] theorem leviInfinite_pair (a : InfiniteLevi F B) (b : FiniteLevi F B) :
    leviInfinite F B (leviPair F B a b) = a :=
  funext fun i => AdelicGL.infinite_pair F (B.size i) (a i) (b i)

@[simp] theorem leviFinite_pair (a : InfiniteLevi F B) (b : FiniteLevi F B) :
    leviFinite F B (leviPair F B a b) = b :=
  funext fun i => AdelicGL.finite_pair F (B.size i) (a i) (b i)

@[simp] theorem leviPair_projections (m : FullLevi F B) :
    leviPair F B (leviInfinite F B m) (leviFinite F B m) = m :=
  funext fun i => AdelicGL.pair_projections F (B.size i) (m i)

theorem continuous_leviPair :
    Continuous (fun p : InfiniteLevi F B × FiniteLevi F B => leviPair F B p.1 p.2) := by
  apply continuous_pi
  intro i
  exact (AdelicGL.continuous_pair F (B.size i)).comp
    (show Continuous (fun p : InfiniteLevi F B × FiniteLevi F B => (p.1 i, p.2 i)) from
      ((continuous_apply i).comp continuous_fst).prodMk
        ((continuous_apply i).comp continuous_snd))

/-- The actual full Levi product is the product of its archimedean and finite factors. -/
def leviSplit : FullLevi F B ≃ₜ* InfiniteLevi F B × FiniteLevi F B where
  toFun m := (leviInfinite F B m, leviFinite F B m)
  invFun p := leviPair F B p.1 p.2
  left_inv := leviPair_projections F B
  right_inv p := Prod.ext (leviInfinite_pair F B p.1 p.2) (leviFinite_pair F B p.1 p.2)
  map_mul' m k := Prod.ext ((leviInfinite F B).map_mul m k) ((leviFinite F B).map_mul m k)
  continuous_toFun := (leviInfinite F B).continuous.prodMk (leviFinite F B).continuous
  continuous_invFun := continuous_leviPair F B

/-- Archimedean projection commutes with extraction of every actual diagonal block. -/
@[simp] theorem leviProjection_infinite (g : Full F B) :
    B.leviProjection (InfiniteAdeleRing F) (infinite F B g) =
      leviInfinite F B (B.leviProjection (AdeleRing (𝓞 F) F) g) := by
  funext i
  apply Units.ext
  ext a b
  rfl

/-- Finite projection commutes with extraction of every actual diagonal block. -/
@[simp] theorem leviProjection_finite (g : Full F B) :
    B.leviProjection (FiniteAdeleRing (𝓞 F) F) (finite F B g) =
      leviFinite F B (B.leviProjection (AdeleRing (𝓞 F) F) g) := by
  funext i
  apply Units.ext
  ext a b
  rfl

/-- Pairing parabolic points pairs their actual Levi blocks. -/
@[simp] theorem leviProjection_pair (a : Infinite F B) (b : Finite F B) :
    B.leviProjection (AdeleRing (𝓞 F) F) (pair F B a b) =
      leviPair F B (B.leviProjection (InfiniteAdeleRing F) a)
        (B.leviProjection (FiniteAdeleRing (𝓞 F) F) b) := by
  funext i
  apply Units.ext
  ext x y
  rfl

private theorem map_leviEmbedding {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : B.Levi R) :
    Matrix.GeneralLinearGroup.map f (B.leviEmbedding R m) =
      B.leviEmbedding S (fun i => Matrix.GeneralLinearGroup.map f (m i)) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change f (B.leviEmbedding R m (B.index i a) (B.index j b)) =
    B.leviEmbedding S (fun k => Matrix.GeneralLinearGroup.map f (m k))
      (B.index i a) (B.index j b)
  by_cases h : i = j
  · subst j
    simp only [B.leviEmbedding_apply_same]
    rfl
  · rw [B.leviEmbedding_apply_ne R m a b h,
      B.leviEmbedding_apply_ne S _ a b h, map_zero]

/-- The actual block diagonal section commutes with archimedean projection. -/
@[simp] theorem infinite_leviInParabolic (m : FullLevi F B) :
    infinite F B (B.leviInParabolic (AdeleRing (𝓞 F) F) m) =
      B.leviInParabolic (InfiniteAdeleRing F) (leviInfinite F B m) :=
  Subtype.ext (map_leviEmbedding B
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) m)

/-- The actual block diagonal section commutes with finite projection. -/
@[simp] theorem finite_leviInParabolic (m : FullLevi F B) :
    finite F B (B.leviInParabolic (AdeleRing (𝓞 F) F) m) =
      B.leviInParabolic (FiniteAdeleRing (𝓞 F) F) (leviFinite F B m) :=
  Subtype.ext (map_leviEmbedding B
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) m)

/-- The two actual splittings commute with the full Levi projection. -/
theorem split_leviProjection (g : Full F B) :
    leviSplit F B (B.leviProjection (AdeleRing (𝓞 F) F) g) =
      (B.leviProjection (InfiniteAdeleRing F) (split F B g).1,
        B.leviProjection (FiniteAdeleRing (𝓞 F) F) (split F B g).2) :=
  Prod.ext (leviProjection_infinite F B g).symm (leviProjection_finite F B g).symm

/-- The two actual splittings commute with the block diagonal section. -/
theorem split_leviInParabolic (m : FullLevi F B) :
    split F B (B.leviInParabolic (AdeleRing (𝓞 F) F) m) =
      (B.leviInParabolic (InfiniteAdeleRing F) (leviSplit F B m).1,
        B.leviInParabolic (FiniteAdeleRing (𝓞 F) F) (leviSplit F B m).2) :=
  Prod.ext (infinite_leviInParabolic F B m) (finite_leviInParabolic F B m)

end Langlands.Global.AdelicBlockParabolic
