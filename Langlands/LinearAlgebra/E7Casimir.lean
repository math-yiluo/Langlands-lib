import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Langlands.LinearAlgebra.RootReflectionCoefficients

/-! # The Casimir identity for root data of type `E₇`

For a root datum over `ℤ` with a base whose Cartan matrix is `CartanMatrix.E 7` and whose
coroots span the cocharacter lattice, every character `x` satisfies
`∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ = 36 x`, the sum running over all roots.
-/

namespace Langlands.E7Casimir

open RootReflectionCoefficients (reflect)

/-- The coefficient vectors, in the simple roots numbered as in `CartanMatrix.E 7`, of the
126 roots of `E₇`, listed in increasing order of `rootKey`. -/
def rootCoeff : Fin 126 → Fin 7 → ℤ := ![
    ![-2, -2, -3, -4, -3, -2, -1],
    ![-1, -2, -3, -4, -3, -2, -1],
    ![-1, -2, -2, -4, -3, -2, -1],
    ![-1, -2, -2, -3, -3, -2, -1],
    ![-1, -1, -2, -3, -3, -2, -1],
    ![-1, -2, -2, -3, -2, -2, -1],
    ![-1, -1, -2, -3, -2, -2, -1],
    ![-1, -1, -2, -2, -2, -2, -1],
    ![-1, -1, -1, -2, -2, -2, -1],
    ![0, -1, -1, -2, -2, -2, -1],
    ![-1, -2, -2, -3, -2, -1, -1],
    ![-1, -1, -2, -3, -2, -1, -1],
    ![-1, -1, -2, -2, -2, -1, -1],
    ![-1, -1, -1, -2, -2, -1, -1],
    ![0, -1, -1, -2, -2, -1, -1],
    ![-1, -1, -2, -2, -1, -1, -1],
    ![-1, -1, -1, -2, -1, -1, -1],
    ![0, -1, -1, -2, -1, -1, -1],
    ![-1, -1, -1, -1, -1, -1, -1],
    ![0, -1, -1, -1, -1, -1, -1],
    ![-1, 0, -1, -1, -1, -1, -1],
    ![0, 0, -1, -1, -1, -1, -1],
    ![0, -1, 0, -1, -1, -1, -1],
    ![0, 0, 0, -1, -1, -1, -1],
    ![0, 0, 0, 0, -1, -1, -1],
    ![0, 0, 0, 0, 0, -1, -1],
    ![0, 0, 0, 0, 0, 0, -1],
    ![-1, -2, -2, -3, -2, -1, 0],
    ![-1, -1, -2, -3, -2, -1, 0],
    ![-1, -1, -2, -2, -2, -1, 0],
    ![-1, -1, -1, -2, -2, -1, 0],
    ![0, -1, -1, -2, -2, -1, 0],
    ![-1, -1, -2, -2, -1, -1, 0],
    ![-1, -1, -1, -2, -1, -1, 0],
    ![0, -1, -1, -2, -1, -1, 0],
    ![-1, -1, -1, -1, -1, -1, 0],
    ![0, -1, -1, -1, -1, -1, 0],
    ![-1, 0, -1, -1, -1, -1, 0],
    ![0, 0, -1, -1, -1, -1, 0],
    ![0, -1, 0, -1, -1, -1, 0],
    ![0, 0, 0, -1, -1, -1, 0],
    ![0, 0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, -1, 0],
    ![-1, -1, -2, -2, -1, 0, 0],
    ![-1, -1, -1, -2, -1, 0, 0],
    ![0, -1, -1, -2, -1, 0, 0],
    ![-1, -1, -1, -1, -1, 0, 0],
    ![0, -1, -1, -1, -1, 0, 0],
    ![-1, 0, -1, -1, -1, 0, 0],
    ![0, 0, -1, -1, -1, 0, 0],
    ![0, -1, 0, -1, -1, 0, 0],
    ![0, 0, 0, -1, -1, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0],
    ![-1, -1, -1, -1, 0, 0, 0],
    ![0, -1, -1, -1, 0, 0, 0],
    ![-1, 0, -1, -1, 0, 0, 0],
    ![0, 0, -1, -1, 0, 0, 0],
    ![0, -1, 0, -1, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0],
    ![-1, 0, -1, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 0, 0],
    ![0, 1, 1, 2, 1, 0, 0],
    ![1, 1, 1, 2, 1, 0, 0],
    ![1, 1, 2, 2, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 1, 1, 1, 0],
    ![0, 1, 0, 1, 1, 1, 0],
    ![0, 0, 1, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1, 0],
    ![1, 1, 1, 1, 1, 1, 0],
    ![0, 1, 1, 2, 1, 1, 0],
    ![1, 1, 1, 2, 1, 1, 0],
    ![1, 1, 2, 2, 1, 1, 0],
    ![0, 1, 1, 2, 2, 1, 0],
    ![1, 1, 1, 2, 2, 1, 0],
    ![1, 1, 2, 2, 2, 1, 0],
    ![1, 1, 2, 3, 2, 1, 0],
    ![1, 2, 2, 3, 2, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 1, 1, 1, 1],
    ![0, 1, 0, 1, 1, 1, 1],
    ![0, 0, 1, 1, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 1],
    ![0, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1],
    ![0, 1, 1, 2, 1, 1, 1],
    ![1, 1, 1, 2, 1, 1, 1],
    ![1, 1, 2, 2, 1, 1, 1],
    ![0, 1, 1, 2, 2, 1, 1],
    ![1, 1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 2, 1, 1],
    ![1, 1, 2, 3, 2, 1, 1],
    ![1, 2, 2, 3, 2, 1, 1],
    ![0, 1, 1, 2, 2, 2, 1],
    ![1, 1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 2, 2, 1],
    ![1, 1, 2, 3, 3, 2, 1],
    ![1, 2, 2, 3, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![2, 2, 3, 4, 3, 2, 1]]

/-- `reflIndex a m` is the position of the reflection of root `a` in the simple root `m`. -/
def reflIndex : Fin 126 → Fin 7 → Fin 126 := ![
    ![1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 2, 1, 1, 1, 1],
    ![2, 2, 1, 3, 2, 2, 2],
    ![3, 4, 3, 2, 5, 3, 3],
    ![4, 3, 4, 4, 6, 4, 4],
    ![5, 6, 5, 5, 3, 10, 5],
    ![6, 5, 6, 7, 4, 11, 6],
    ![7, 7, 8, 6, 7, 12, 7],
    ![9, 8, 7, 8, 8, 13, 8],
    ![8, 9, 9, 9, 9, 14, 9],
    ![10, 11, 10, 10, 10, 5, 27],
    ![11, 10, 11, 12, 11, 6, 28],
    ![12, 12, 13, 11, 15, 7, 29],
    ![14, 13, 12, 13, 16, 8, 30],
    ![13, 14, 14, 14, 17, 9, 31],
    ![15, 15, 16, 15, 12, 15, 32],
    ![17, 16, 15, 18, 13, 16, 33],
    ![16, 17, 17, 19, 14, 17, 34],
    ![19, 20, 18, 16, 18, 18, 35],
    ![18, 21, 22, 17, 19, 19, 36],
    ![21, 18, 20, 20, 20, 20, 37],
    ![20, 19, 23, 21, 21, 21, 38],
    ![22, 23, 19, 22, 22, 22, 39],
    ![23, 22, 21, 24, 23, 23, 40],
    ![24, 24, 24, 23, 25, 24, 41],
    ![25, 25, 25, 25, 24, 26, 42],
    ![26, 26, 26, 26, 26, 25, 99],
    ![27, 28, 27, 27, 27, 27, 10],
    ![28, 27, 28, 29, 28, 28, 11],
    ![29, 29, 30, 28, 32, 29, 12],
    ![31, 30, 29, 30, 33, 30, 13],
    ![30, 31, 31, 31, 34, 31, 14],
    ![32, 32, 33, 32, 29, 43, 15],
    ![34, 33, 32, 35, 30, 44, 16],
    ![33, 34, 34, 36, 31, 45, 17],
    ![36, 37, 35, 33, 35, 46, 18],
    ![35, 38, 39, 34, 36, 47, 19],
    ![38, 35, 37, 37, 37, 48, 20],
    ![37, 36, 40, 38, 38, 49, 21],
    ![39, 40, 36, 39, 39, 50, 22],
    ![40, 39, 38, 41, 40, 51, 23],
    ![41, 41, 41, 40, 42, 52, 24],
    ![42, 42, 42, 42, 41, 83, 25],
    ![43, 43, 44, 43, 43, 32, 43],
    ![45, 44, 43, 46, 44, 33, 44],
    ![44, 45, 45, 47, 45, 34, 45],
    ![47, 48, 46, 44, 53, 35, 46],
    ![46, 49, 50, 45, 54, 36, 47],
    ![49, 46, 48, 48, 55, 37, 48],
    ![48, 47, 51, 49, 56, 38, 49],
    ![50, 51, 47, 50, 57, 39, 50],
    ![51, 50, 49, 52, 58, 40, 51],
    ![52, 52, 52, 51, 73, 41, 52],
    ![54, 55, 53, 53, 46, 53, 53],
    ![53, 56, 57, 54, 47, 54, 54],
    ![56, 53, 55, 59, 48, 55, 55],
    ![55, 54, 58, 60, 49, 56, 56],
    ![57, 58, 54, 61, 50, 57, 57],
    ![58, 57, 56, 67, 51, 58, 58],
    ![60, 59, 62, 55, 59, 59, 59],
    ![59, 60, 65, 56, 60, 60, 60],
    ![61, 64, 61, 57, 61, 61, 61],
    ![63, 62, 59, 62, 62, 62, 62],
    ![62, 63, 66, 63, 63, 63, 63],
    ![64, 61, 64, 68, 64, 64, 64],
    ![66, 65, 60, 69, 65, 65, 65],
    ![65, 66, 63, 70, 66, 66, 66],
    ![67, 68, 69, 58, 74, 67, 67],
    ![68, 67, 71, 64, 75, 68, 68],
    ![70, 71, 67, 65, 76, 69, 69],
    ![69, 72, 70, 66, 77, 70, 70],
    ![72, 69, 68, 71, 78, 71, 71],
    ![71, 70, 72, 72, 79, 72, 72],
    ![73, 73, 73, 74, 52, 84, 73],
    ![74, 75, 76, 73, 67, 85, 74],
    ![75, 74, 78, 75, 68, 86, 75],
    ![77, 78, 74, 76, 69, 87, 76],
    ![76, 79, 77, 77, 70, 88, 77],
    ![79, 76, 75, 80, 71, 89, 78],
    ![78, 77, 79, 81, 72, 90, 79],
    ![81, 80, 80, 78, 80, 91, 80],
    ![80, 81, 82, 79, 81, 92, 81],
    ![82, 82, 81, 82, 82, 93, 82],
    ![83, 83, 83, 83, 84, 42, 100],
    ![84, 84, 84, 85, 83, 73, 101],
    ![85, 86, 87, 84, 85, 74, 102],
    ![86, 85, 89, 86, 86, 75, 103],
    ![88, 89, 85, 87, 87, 76, 104],
    ![87, 90, 88, 88, 88, 77, 105],
    ![90, 87, 86, 91, 89, 78, 106],
    ![89, 88, 90, 92, 90, 79, 107],
    ![92, 91, 91, 89, 94, 80, 108],
    ![91, 92, 93, 90, 95, 81, 109],
    ![93, 93, 92, 93, 96, 82, 110],
    ![95, 94, 94, 94, 91, 94, 111],
    ![94, 95, 96, 95, 92, 95, 112],
    ![96, 96, 95, 97, 93, 96, 113],
    ![97, 98, 97, 96, 97, 97, 114],
    ![98, 97, 98, 98, 98, 98, 115],
    ![99, 99, 99, 99, 99, 100, 26],
    ![100, 100, 100, 100, 101, 99, 83],
    ![101, 101, 101, 102, 100, 101, 84],
    ![102, 103, 104, 101, 102, 102, 85],
    ![103, 102, 106, 103, 103, 103, 86],
    ![105, 106, 102, 104, 104, 104, 87],
    ![104, 107, 105, 105, 105, 105, 88],
    ![107, 104, 103, 108, 106, 106, 89],
    ![106, 105, 107, 109, 107, 107, 90],
    ![109, 108, 108, 106, 111, 108, 91],
    ![108, 109, 110, 107, 112, 109, 92],
    ![110, 110, 109, 110, 113, 110, 93],
    ![112, 111, 111, 111, 108, 116, 94],
    ![111, 112, 113, 112, 109, 117, 95],
    ![113, 113, 112, 114, 110, 118, 96],
    ![114, 115, 114, 113, 114, 119, 97],
    ![115, 114, 115, 115, 115, 120, 98],
    ![117, 116, 116, 116, 116, 111, 116],
    ![116, 117, 118, 117, 117, 112, 117],
    ![118, 118, 117, 119, 118, 113, 118],
    ![119, 120, 119, 118, 121, 114, 119],
    ![120, 119, 120, 120, 122, 115, 120],
    ![121, 122, 121, 121, 119, 121, 121],
    ![122, 121, 122, 123, 120, 122, 122],
    ![123, 123, 124, 122, 123, 123, 123],
    ![125, 124, 123, 124, 124, 124, 124],
    ![124, 125, 125, 125, 125, 125, 125]]

/-- `negIndex a` is the position of the negative of root `a`. -/
def negIndex : Fin 126 → Fin 126 :=
  ![125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110,
    109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94,
    93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78,
    77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62,
    61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46,
    45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30,
    29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14,
    13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

/-- `simpleIndex k` is the position of the simple root `k`. -/
def simpleIndex : Fin 7 → Fin 126 := ![63, 64, 65, 67, 73, 83, 99]

/-- The number of simple reflections needed to reach root `a` from a simple root. -/
def depth : Fin 126 → ℕ :=
  ![17, 16, 15, 14, 13, 13, 12, 11, 10, 9, 12, 11, 10, 9, 8, 9, 8, 7, 7, 6,
    6, 5, 5, 4, 3, 2, 1, 11, 10, 9, 8, 7, 8, 7, 6, 6, 5, 5, 4, 4,
    3, 2, 1, 7, 6, 5, 5, 4, 4, 3, 3, 2, 1, 4, 3, 3, 2, 2, 1, 2,
    1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 2, 2, 3, 0, 1, 2, 2, 3, 3, 4,
    4, 5, 6, 0, 1, 2, 3, 3, 4, 4, 5, 5, 6, 7, 6, 7, 8, 9, 10, 0,
    1, 2, 3, 4, 4, 5, 5, 6, 6, 7, 8, 7, 8, 9, 10, 11, 8, 9, 10, 11,
    12, 12, 13, 14, 15, 16]

/-- A root of smaller depth from which root `a` is obtained by one simple reflection
(root `a` itself when `a` is simple). -/
def parent : Fin 126 → Fin 126 :=
  ![1, 2, 3, 5, 6, 10, 11, 12, 13, 14, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
    37, 38, 39, 40, 41, 42, 99, 28, 29, 32, 33, 34, 43, 44, 45, 46, 47, 48, 49, 50,
    51, 52, 83, 44, 46, 47, 53, 54, 55, 56, 57, 58, 73, 55, 57, 59, 60, 61, 67, 62,
    65, 64, 63, 63, 64, 65, 63, 67, 64, 65, 66, 68, 70, 73, 67, 68, 69, 70, 71, 72,
    78, 79, 81, 83, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 91, 92, 93, 96, 97, 99,
    83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 111, 112, 113, 114,
    115, 119, 120, 122, 123, 124]

/-- The simple root whose reflection carries `parent a` to `a` (for a simple root `a`, its own
vertex). -/
def parentVertex : Fin 126 → Fin 7 :=
  ![0, 2, 3, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 1, 3, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5,
    5, 5, 5, 2, 3, 3, 4, 4, 4, 4, 4, 4, 4, 1, 2, 3, 3, 3, 3, 2,
    2, 1, 0, 0, 1, 2, 2, 3, 3, 3, 3, 2, 1, 4, 4, 4, 4, 4, 4, 4,
    3, 3, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 3, 1, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5,
    5, 4, 4, 3, 2, 0]

/-- The weight `∑ₖ cₖ 9ᵏ` of a coefficient vector; the list `rootCoeff` increases strictly in it. -/
def rootKey (c : Fin 7 → ℤ) : ℤ := ∑ k, c k * 9 ^ (k : ℕ)

theorem rootCoeff_reflIndex (a : Fin 126) (m : Fin 7) :
    rootCoeff (reflIndex a m) = reflect (CartanMatrix.E 7) m (rootCoeff a) := by
  revert a m
  decide +kernel

theorem rootCoeff_negIndex (a : Fin 126) : rootCoeff (negIndex a) = -rootCoeff a := by
  revert a
  decide +kernel

theorem rootCoeff_simpleIndex (k : Fin 7) : rootCoeff (simpleIndex k) = Pi.single k 1 := by
  revert k
  decide +kernel

theorem parent_spec (a : Fin 126) :
    (depth a = 0 ∧ rootCoeff a = Pi.single (parentVertex a) 1) ∨
      (depth (parent a) < depth a ∧
        rootCoeff a = reflect (CartanMatrix.E 7) (parentVertex a) (rootCoeff (parent a))) := by
  revert a
  decide +kernel

theorem rootKey_lt (a : Fin 125) : rootKey (rootCoeff a.castSucc) < rootKey (rootCoeff a.succ) := by
  revert a
  decide +kernel

theorem sum_rootCoeff_mul (k j : Fin 7) :
    ∑ a, rootCoeff a k * ∑ l, rootCoeff a l * CartanMatrix.E 7 l j = if k = j then 36 else 0 := by
  revert k j
  decide +kernel

theorem rootCoeff_injective : Function.Injective rootCoeff := by
  have : StrictMono fun a => rootKey (rootCoeff a) :=
    Fin.strictMono_iff_lt_succ.mpr rootKey_lt
  exact Function.Injective.of_comp (f := rootKey) this.injective

section RootDatum

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootDatum ι M N)
  (s : Fin 7 → ι)

/-- The integral combination `∑ₖ cₖ α_{s k}` of the selected roots. -/
def comb (c : Fin 7 → ℤ) : M := ∑ k, c k • P.root (s k)

/-- The integral combination `∑ₖ cₖ α_{s k}^∨` of the selected coroots. -/
def cocomb (c : Fin 7 → ℤ) : N := ∑ k, c k • P.coroot (s k)

variable {P s}

theorem comb_neg (c : Fin 7 → ℤ) : comb P s (-c) = -comb P s c := by
  simp [comb, neg_smul, Finset.sum_neg_distrib]

theorem cocomb_neg (c : Fin 7 → ℤ) : cocomb P s (-c) = -cocomb P s c := by
  simp [cocomb, neg_smul, Finset.sum_neg_distrib]

theorem comb_single (k : Fin 7) : comb P s (Pi.single k 1) = P.root (s k) := by
  classical
  simp [comb, Pi.single_apply, ite_smul]

theorem cocomb_single (k : Fin 7) : cocomb P s (Pi.single k 1) = P.coroot (s k) := by
  classical
  simp [cocomb, Pi.single_apply, ite_smul]

variable (hA : ∀ i j, P.pairing (s i) (s j) = CartanMatrix.E 7 i j)
include hA

theorem toLinearMap_comb_coroot (c : Fin 7 → ℤ) (m : Fin 7) :
    P.toLinearMap (comb P s c) (P.coroot (s m)) = ∑ k, c k * CartanMatrix.E 7 k m := by
  simp only [comb, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    RootPairing.root_coroot_eq_pairing, hA, smul_eq_mul]

theorem toLinearMap_root_cocomb (c : Fin 7 → ℤ) (m : Fin 7) :
    P.toLinearMap (P.root (s m)) (cocomb P s c) = ∑ k, c k * CartanMatrix.E 7 k m := by
  simp only [cocomb, map_sum, map_zsmul, RootPairing.root_coroot_eq_pairing, hA, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← CartanMatrix.E_transpose 7, Matrix.transpose_apply, CartanMatrix.E_transpose]

/-- Reflection in a selected simple root acts on coefficient vectors by `reflect`. -/
theorem reflectionPerm_spec {r : ι} {c : Fin 7 → ℤ} (h₁ : P.root r = comb P s c)
    (h₂ : P.coroot r = cocomb P s c) (m : Fin 7) :
    P.root (P.reflectionPerm (s m) r) = comb P s (reflect (CartanMatrix.E 7) m c) ∧
      P.coroot (P.reflectionPerm (s m) r) = cocomb P s (reflect (CartanMatrix.E 7) m c) := by
  constructor
  · have hp : P.pairing r (s m) = ∑ k, c k * CartanMatrix.E 7 k m := by
      rw [← RootPairing.root_coroot_eq_pairing, h₁, toLinearMap_comb_coroot hA]
    rw [P.root_reflectionPerm, P.reflection_apply_root, hp, h₁]
    simp [comb, reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]
  · have hp : P.pairing (s m) r = ∑ k, c k * CartanMatrix.E 7 k m := by
      rw [← RootPairing.root_coroot_eq_pairing, h₂, toLinearMap_root_cocomb hA]
    rw [P.coroot_reflectionPerm, P.coreflection_apply_coroot, hp, h₂]
    simp [cocomb, reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]

/-- Every listed coefficient vector is that of an actual root and its coroot. -/
theorem exists_index (a : Fin 126) :
    ∃ r : ι, P.root r = comb P s (rootCoeff a) ∧ P.coroot r = cocomb P s (rootCoeff a) := by
  induction h : depth a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    rcases parent_spec a with ⟨-, hc⟩ | ⟨hlt, hc⟩
    · exact ⟨s (parentVertex a), by rw [hc, comb_single], by rw [hc, cocomb_single]⟩
    · obtain ⟨r, h₁, h₂⟩ := ih _ (h ▸ hlt) (parent a) rfl
      rw [hc]
      exact ⟨_, reflectionPerm_spec hA h₁ h₂ (parentVertex a)⟩

/-- Every root has a listed coefficient vector, simultaneously for the root and its coroot. -/
theorem exists_rootCoeff [Finite ι] [P.IsReduced] (b : P.Base)
    (hsupp : ∀ i ∈ b.support, ∃ k, s k = i) (r : ι) :
    ∃ a, P.root r = comb P s (rootCoeff a) ∧ P.coroot r = cocomb P s (rootCoeff a) := by
  refine b.induction_reflect (p := fun r => ∃ a, P.root r = comb P s (rootCoeff a) ∧
    P.coroot r = cocomb P s (rootCoeff a)) r ?_ ?_ ?_
  · rintro i ⟨a, h₁, h₂⟩
    refine ⟨negIndex a, ?_, ?_⟩
    · rw [P.root_reflectionPerm, P.reflection_apply_self, h₁, rootCoeff_negIndex, comb_neg]
    · rw [P.coroot_reflectionPerm, P.coreflection_apply_self, h₂, rootCoeff_negIndex, cocomb_neg]
  · intro i hi
    obtain ⟨k, rfl⟩ := hsupp i hi
    exact ⟨simpleIndex k, by rw [rootCoeff_simpleIndex, comb_single],
      by rw [rootCoeff_simpleIndex, cocomb_single]⟩
  · rintro i j ⟨a, h₁, h₂⟩ hj
    obtain ⟨m, rfl⟩ := hsupp j hj
    exact ⟨reflIndex a m, by rw [rootCoeff_reflIndex]; exact (reflectionPerm_spec hA h₁ h₂ m).1,
      by rw [rootCoeff_reflIndex]; exact (reflectionPerm_spec hA h₁ h₂ m).2⟩

theorem injective_of_cartan : Function.Injective s := by
  intro i j hij
  by_contra hne
  have h := hA i j
  rw [hij, P.pairing_same] at h
  have := CartanMatrix.E_off_diag_nonpos 7 i j hne
  lia

/-- **The Casimir identity for `E₇`.** For a reduced root datum over `ℤ` with a base whose
simple roots, numbered by `s`, have Cartan matrix `CartanMatrix.E 7`, and whose coroots span the
cocharacter lattice, every character `x` satisfies `∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ = 36 x`. -/
theorem sum_toLinearMap_coroot_smul_root [Fintype ι] [P.IsReduced] (b : P.Base)
    (hs : ∀ k, s k ∈ b.support) (hsupp : ∀ i ∈ b.support, ∃ k, s k = i)
    (hspan : P.corootSpan ℤ = ⊤) (x : M) :
    ∑ i, P.toLinearMap x (P.coroot i) • P.root i = (36 : ℤ) • x := by
  classical
  choose φ hφ₁ hφ₂ using exists_index (P := P) (s := s) hA
  have hlin : LinearIndependent ℤ fun k => P.root (s k) :=
    b.linearIndepOn_root.comp (fun k => ⟨s k, hs k⟩)
      (fun i j h => injective_of_cartan hA (congrArg Subtype.val h))
  have hφinj : Function.Injective φ := by
    intro a a' h
    apply rootCoeff_injective
    funext k
    have := congrArg P.root h
    rw [hφ₁, hφ₁] at this
    exact Fintype.linearIndependent_iffₛ.mp hlin _ _ this k
  have hφsurj : Function.Surjective φ := by
    intro r
    obtain ⟨a, h₁, -⟩ := exists_rootCoeff hA b hsupp r
    exact ⟨a, P.root.injective (by rw [hφ₁, h₁])⟩
  have hsum : ∑ i, P.toLinearMap x (P.coroot i) • P.root i =
      ∑ a, P.toLinearMap x (cocomb P s (rootCoeff a)) • comb P s (rootCoeff a) :=
    (Fintype.sum_bijective φ ⟨hφinj, hφsurj⟩ _ _ (fun a => by rw [hφ₁, hφ₂])).symm
  rw [hsum]
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).1
  have hspan' : Submodule.span ℤ (P.coroot '' b.support) = ⊤ := by
    rw [b.span_int_coroot_support]
    exact hspan
  refine LinearMap.ext_on hspan' ?_
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨j, rfl⟩ := hsupp i hi
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    toLinearMap_comb_coroot hA, smul_eq_mul, cocomb]
  calc ∑ a, (∑ k, rootCoeff a k * P.toLinearMap x (P.coroot (s k))) *
        ∑ l, rootCoeff a l * CartanMatrix.E 7 l j
      = ∑ k, P.toLinearMap x (P.coroot (s k)) *
          ∑ a, rootCoeff a k * ∑ l, rootCoeff a l * CartanMatrix.E 7 l j := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun l _ => by ring
    _ = 36 * P.toLinearMap x (P.coroot (s j)) := by
        simp_rw [sum_rootCoeff_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]
        ring

end RootDatum

section Equiv

variable {ι M N ι₂ M₂ N₂ : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M₂]
  [AddCommGroup N₂] {P : RootDatum ι M N} {Q : RootDatum ι₂ M₂ N₂}

/-- An equivalence of root data preserves the pairing of a character with a coroot:
`⟨W x, α^∨_{σ i}⟩ = ⟨x, α^∨_i⟩` for its weight map `W` and index bijection `σ`. -/
theorem toLinearMap_weightMap_coroot_indexEquiv (f : RootPairing.Equiv P Q) (x : M) (i : ι) :
    Q.toLinearMap (f.weightMap x) (Q.coroot (f.indexEquiv i)) = P.toLinearMap x (P.coroot i) := by
  have hj : f.coweightMap (Q.coroot (f.indexEquiv i)) = P.coroot i := by
    simpa using RootPairing.Hom.coroot_coweightMap_apply P Q (f.indexEquiv i) f.toHom
  simpa [← hj] using congr($(f.weight_coweight_transpose) (Q.coroot (f.indexEquiv i)) x)

/-- The sum `∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ` is carried by the weight map of an equivalence of root data to the
corresponding sum of the target. -/
theorem weightMap_sum_toLinearMap_coroot_smul_root [Fintype ι] [Fintype ι₂]
    (f : RootPairing.Equiv P Q) (x : M) :
    f.weightMap (∑ i, P.toLinearMap x (P.coroot i) • P.root i) =
      ∑ j, Q.toLinearMap (f.weightMap x) (Q.coroot j) • Q.root j := by
  rw [map_sum, ← f.indexEquiv.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, toLinearMap_weightMap_coroot_indexEquiv,
    RootPairing.Hom.root_weightMap_apply]

/-- The identity `∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ = c x` passes from a root datum to an equivalent one. -/
theorem sum_toLinearMap_coroot_smul_root_of_equiv [Fintype ι] [Fintype ι₂]
    (f : RootPairing.Equiv P Q) (c : ℤ)
    (h : ∀ x, ∑ i, P.toLinearMap x (P.coroot i) • P.root i = c • x) (y : M₂) :
    ∑ j, Q.toLinearMap y (Q.coroot j) • Q.root j = c • y := by
  obtain ⟨x, rfl⟩ := f.bijective_weightMap.2 y
  rw [← weightMap_sum_toLinearMap_coroot_smul_root, h, map_zsmul]

/-- The identity `∑ᵢ ⟨x, αᵢ^∨⟩ αᵢ = c x` passes back along an equivalence of root data. -/
theorem sum_toLinearMap_coroot_smul_root_of_equiv_symm [Fintype ι] [Fintype ι₂]
    (f : RootPairing.Equiv P Q) (c : ℤ)
    (h : ∀ y, ∑ j, Q.toLinearMap y (Q.coroot j) • Q.root j = c • y) (x : M) :
    ∑ i, P.toLinearMap x (P.coroot i) • P.root i = c • x := by
  apply f.bijective_weightMap.1
  rw [weightMap_sum_toLinearMap_coroot_smul_root, h, map_zsmul]

end Equiv

end Langlands.E7Casimir
