# Integrating entire Mellin fibers

`archimedeanMellinMarginal` integrates an entire family over a common outer parameter space. It assumes exponential growth in each fiber and two product Mellin formulas, one for the ordinary argument and one for the reflected argument. The product kernels have absolute moments at every sufficiently large real exponent.

Fubini at countably many real exponents and interpolation between the resulting powers give a common open right half-plane of holomorphy for almost every fiber integral. The identity theorem extends both formulas to that half-plane. Bounds on the two endpoint multipliers and Fubini give the integrable vertical-line majorants used by `Langlands.Analysis.entireStripIntegral`. A final Fubini calculation identifies the integrated entire family on the ordinary right half-plane.
