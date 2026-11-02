import Langlands.Representation.CuspidalSupport.JacquetLengthDetector

/-!
# Jacquet images of subrepresentations

For a smooth representation `π` of `GL_n` and a block shape `C`, send a
subrepresentation `X` of `π` to the image of its normalized Jacquet module in
that of `π`. By exactness of the Jacquet functor this map is monotone, preserves
intersections, identifies the image with the Jacquet module of `X`, and is
strictly monotone as soon as every nonzero step quotient has a nonzero Jacquet
module.
-/

noncomputable section

open Representation

namespace Langlands.Classification.JuxtaposedShuffle

open GeneralLinear CuspidalSupport.JacquetLength

universe uF uU uV uW

section Range

variable {k : Type*} [Field k] {G : Type*} [Monoid G] {U : Type uU} {W : Type uW}
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  {ρ : Representation k G U} {σ : Representation k G W}

/-- An injective intertwiner identifies its source with its range. -/
def rangeEquivOfInjective (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    ρ.Equiv f.range.toRepresentation :=
  Representation.Equiv.mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g => by
    ext w
    exact IntertwiningMap.isIntertwining _ _ f g w

end Range

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GeneralLinear n F.Carrier) V}

/-- The normalized Jacquet map of an injective intertwiner into a smooth
representation is injective. -/
theorem normalizedJacquetMap_injective {U : Type uU} {W : Type uW}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) U}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W}
    (hσ : letI := T.topology; IsSmooth σ) (i : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) :
    Function.Injective (T.normalizedJacquetMap C i) := by
  let q : σ.IntertwiningMap (σ.quotient i.range.toSubmodule
      (fun g _ hv => i.range.apply_mem_toSubmodule g hv)) :=
    { toLinearMap := i.range.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  exact (T.normalizedJacquetMap_exact C i q hσ hi (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm).1

/-- The image of the normalized Jacquet module of `X` in that of `π`. -/
def jacquetImage (X : Subrepresentation π) : Subrepresentation (T.normalizedJacquet C π) :=
  (T.normalizedJacquetMap C (subtypeMap X)).range

theorem mem_jacquetImage {X : Subrepresentation π} {w : C.JacquetModule π} :
    w ∈ jacquetImage T C X ↔ ∃ x ∈ X, C.jacquetMk π x = w := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := C.jacquetMk_surjective X.toRepresentation u
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨C.jacquetMk X.toRepresentation ⟨x, hx⟩, rfl⟩

theorem jacquetImage_mono {X Y : Subrepresentation π} (h : X ≤ Y) :
    jacquetImage T C X ≤ jacquetImage T C Y := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := (mem_jacquetImage T C).1 hw
  exact (mem_jacquetImage T C).2 ⟨x, h hx, rfl⟩

theorem jacquetImage_top : jacquetImage T C (⊤ : Subrepresentation π) = ⊤ := by
  refine top_unique fun w _ => ?_
  obtain ⟨v, rfl⟩ := C.jacquetMk_surjective π w
  exact (mem_jacquetImage T C).2 ⟨v, trivial, rfl⟩

/-- The Jacquet module of a subrepresentation of a smooth representation is
equivalent to its image. -/
def jacquetImageEquiv (hπ : letI := T.topology; IsSmooth π) (X : Subrepresentation π) :
    (T.normalizedJacquet C X.toRepresentation).Equiv (jacquetImage T C X).toRepresentation :=
  rangeEquivOfInjective _
    (normalizedJacquetMap_injective T C hπ (subtypeMap X) (subtypeMap_injective X))

/-- Jacquet images of a smooth representation preserve intersections. -/
theorem jacquetImage_inf (hπ : letI := T.topology; IsSmooth π) (X Y : Subrepresentation π) :
    jacquetImage T C (X ⊓ Y) = jacquetImage T C X ⊓ jacquetImage T C Y := by
  let := T.topology
  refine le_antisymm (le_inf (jacquetImage_mono T C inf_le_left)
    (jacquetImage_mono T C inf_le_right)) ?_
  rintro w ⟨hwX, hwY⟩
  obtain ⟨x, hx, rfl⟩ := (mem_jacquetImage T C).1 hwX
  obtain ⟨y, hy, hxy⟩ := (mem_jacquetImage T C).1 hwY
  let QY := π.quotient Y.toSubmodule (fun g _ hv => Y.apply_mem_toSubmodule g hv)
  let qY : π.IntertwiningMap QY :=
    { toLinearMap := Y.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  let K := Y.toSubmodule.comap X.toSubmodule.subtype
  let K' : Subrepresentation X.toRepresentation :=
    ⟨K, fun g _ hv => Y.apply_mem_toSubmodule g hv⟩
  let qX : X.toRepresentation.IntertwiningMap (stepQuotient Y X) :=
    { toLinearMap := K.mkQ
      isIntertwining' := fun _ => rfl }
  let j : (stepQuotient Y X).IntertwiningMap QY :=
    { toLinearMap := K.mapQ Y.toSubmodule X.toSubmodule.subtype le_rfl
      isIntertwining' := fun g => Submodule.linearMap_qext _ rfl }
  have hj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun a ha => ?_
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.mkQ_surjective K a
    have hvY : v ∈ Y.toSubmodule := (Submodule.Quotient.mk_eq_zero _).1 ha
    exact (Submodule.Quotient.mk_eq_zero K).2 hvY
  have hQY : IsSmooth QY := isSmooth_of_surjective qY (Submodule.mkQ_surjective _) hπ
  have hXs : IsSmooth X.toRepresentation :=
    isSmooth_of_injective (subtypeMap X) (subtypeMap_injective X) hπ
  have h1 : T.normalizedJacquetMap C j
      (T.normalizedJacquetMap C qX (C.jacquetMk X.toRepresentation ⟨x, hx⟩)) = 0 := by
    change T.normalizedJacquetMap C qY (C.jacquetMk π x) = 0
    rw [← hxy]
    change C.jacquetMk QY (Submodule.Quotient.mk y) = 0
    rw [(Submodule.Quotient.mk_eq_zero _).2 hy, map_zero]
  have h2 : T.normalizedJacquetMap C qX (C.jacquetMk X.toRepresentation ⟨x, hx⟩) = 0 :=
    normalizedJacquetMap_injective T C hQY j hj (h1.trans (map_zero _).symm)
  obtain ⟨-, hex, -⟩ := T.normalizedJacquetMap_exact C (subtypeMap K') qX hXs
    (subtypeMap_injective K') (Submodule.mkQ_surjective _) (by
      change LinearMap.range K.subtype = LinearMap.ker K.mkQ
      rw [Submodule.range_subtype, Submodule.ker_mkQ])
  have h3 : C.jacquetMk X.toRepresentation ⟨x, hx⟩ ∈
      LinearMap.range (T.normalizedJacquetMap C (subtypeMap K')).toLinearMap := by
    rw [hex]
    exact h2
  obtain ⟨t, ht⟩ := h3
  obtain ⟨⟨⟨z, hzX⟩, hzY⟩, rfl⟩ := C.jacquetMk_surjective K'.toRepresentation t
  refine (mem_jacquetImage T C).2 ⟨z, Submodule.mem_inf.2 ⟨hzX, hzY⟩, ?_⟩
  exact congrArg (T.normalizedJacquetMap C (subtypeMap X)) ht

/-- Jacquet images of a smooth representation are strictly monotone when every
nonzero step quotient has a nonzero Jacquet module. -/
theorem jacquetImage_strictMono (hπ : letI := T.topology; IsSmooth π)
    (hpos : ∀ X Y : Subrepresentation π, X ≤ Y →
      Nontrivial (Y.toSubmodule ⧸ X.toSubmodule.comap Y.toSubmodule.subtype) →
      Nontrivial (C.JacquetModule (stepQuotient X Y))) :
    StrictMono (jacquetImage T C (π := π)) := by
  intro X Y hlt
  refine lt_of_le_of_ne (jacquetImage_mono T C hlt.le) fun heq => ?_
  have hnt : Nontrivial (Y.toSubmodule ⧸ X.toSubmodule.comap Y.toSubmodule.subtype) := by
    obtain ⟨v, hvY, hvX⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨Submodule.Quotient.mk ⟨v, hvY⟩, 0, fun h => hvX ?_⟩⟩
    exact (Submodule.Quotient.mk_eq_zero (X.toSubmodule.comap Y.toSubmodule.subtype)).mp h
  obtain ⟨a, b, hab⟩ := (hpos X Y hlt.le hnt).exists_pair_ne
  let qY : Y.toRepresentation.IntertwiningMap (stepQuotient X Y) :=
    { toLinearMap := (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ
      isIntertwining' := fun _ => rfl }
  have hinj := normalizedJacquetMap_injective T C hπ (subtypeMap Y) (subtypeMap_injective Y)
  have h0 : ∀ c : C.JacquetModule (stepQuotient X Y), c = 0 := by
    intro c
    obtain ⟨c, rfl⟩ := C.jacquetMk_surjective _ c
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.mkQ_surjective _ c
    have hmem : C.jacquetMk π y ∈ jacquetImage T C X :=
      heq ▸ (mem_jacquetImage T C).2 ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := (mem_jacquetImage T C).1 hmem
    have h1 : C.jacquetMk Y.toRepresentation ⟨x, hlt.le hx⟩ =
        C.jacquetMk Y.toRepresentation ⟨y, hy⟩ := hinj hxy
    have h2 := congrArg (T.normalizedJacquetMap C qY) h1
    change C.jacquetMk (stepQuotient X Y) (Submodule.Quotient.mk ⟨x, hlt.le hx⟩) =
      C.jacquetMk (stepQuotient X Y) (Submodule.Quotient.mk ⟨y, hy⟩) at h2
    change C.jacquetMk (stepQuotient X Y) (Submodule.Quotient.mk ⟨y, hy⟩) = 0
    rw [← h2, (Submodule.Quotient.mk_eq_zero (X.toSubmodule.comap Y.toSubmodule.subtype)
      (x := ⟨x, hlt.le hx⟩)).2 hx, map_zero]
  exact hab ((h0 a).trans (h0 b).symm)

end Langlands.Classification.JuxtaposedShuffle
